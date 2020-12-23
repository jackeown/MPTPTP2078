%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:09 EST 2020

% Result     : Theorem 11.92s
% Output     : CNFRefutation 11.99s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 454 expanded)
%              Number of leaves         :   25 ( 173 expanded)
%              Depth                    :   14
%              Number of atoms          :  207 (1380 expanded)
%              Number of equality atoms :   54 ( 463 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_7 > #skF_3 > #skF_5 > #skF_8 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_67,axiom,(
    ! [A,B] :
    ? [C] :
      ( v1_relat_1(C)
      & v1_funct_1(C)
      & k1_relat_1(C) = A
      & ! [D] :
          ( r2_hidden(D,A)
         => k1_funct_1(C,D) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_55,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( B = k2_relat_1(A)
        <=> ! [C] :
              ( r2_hidden(C,B)
            <=> ? [D] :
                  ( r2_hidden(D,k1_relat_1(A))
                  & C = k1_funct_1(A,D) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

tff(f_85,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( ~ ( A = k1_xboole_0
              & B != k1_xboole_0 )
          & ! [C] :
              ( ( v1_relat_1(C)
                & v1_funct_1(C) )
             => ~ ( B = k1_relat_1(C)
                  & r1_tarski(k2_relat_1(C),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_funct_1)).

tff(f_40,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_40,plain,(
    ! [A_49,B_50] : v1_relat_1('#skF_6'(A_49,B_50)) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_38,plain,(
    ! [A_49,B_50] : v1_funct_1('#skF_6'(A_49,B_50)) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_36,plain,(
    ! [A_49,B_50] : k1_relat_1('#skF_6'(A_49,B_50)) = A_49 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_22484,plain,(
    ! [A_3773,C_3774] :
      ( r2_hidden('#skF_5'(A_3773,k2_relat_1(A_3773),C_3774),k1_relat_1(A_3773))
      | ~ r2_hidden(C_3774,k2_relat_1(A_3773))
      | ~ v1_funct_1(A_3773)
      | ~ v1_relat_1(A_3773) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_34,plain,(
    ! [A_49,B_50,D_55] :
      ( k1_funct_1('#skF_6'(A_49,B_50),D_55) = B_50
      | ~ r2_hidden(D_55,A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_22441,plain,(
    ! [A_3762,D_3763] :
      ( r2_hidden(k1_funct_1(A_3762,D_3763),k2_relat_1(A_3762))
      | ~ r2_hidden(D_3763,k1_relat_1(A_3762))
      | ~ v1_funct_1(A_3762)
      | ~ v1_relat_1(A_3762) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_22446,plain,(
    ! [B_50,A_49,D_55] :
      ( r2_hidden(B_50,k2_relat_1('#skF_6'(A_49,B_50)))
      | ~ r2_hidden(D_55,k1_relat_1('#skF_6'(A_49,B_50)))
      | ~ v1_funct_1('#skF_6'(A_49,B_50))
      | ~ v1_relat_1('#skF_6'(A_49,B_50))
      | ~ r2_hidden(D_55,A_49) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_22441])).

tff(c_22449,plain,(
    ! [B_50,A_49,D_55] :
      ( r2_hidden(B_50,k2_relat_1('#skF_6'(A_49,B_50)))
      | ~ r2_hidden(D_55,A_49) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_22446])).

tff(c_28636,plain,(
    ! [B_5161,A_5162,C_5163] :
      ( r2_hidden(B_5161,k2_relat_1('#skF_6'(k1_relat_1(A_5162),B_5161)))
      | ~ r2_hidden(C_5163,k2_relat_1(A_5162))
      | ~ v1_funct_1(A_5162)
      | ~ v1_relat_1(A_5162) ) ),
    inference(resolution,[status(thm)],[c_22484,c_22449])).

tff(c_29215,plain,(
    ! [B_5235,A_5236,B_5237] :
      ( r2_hidden(B_5235,k2_relat_1('#skF_6'(k1_relat_1(A_5236),B_5235)))
      | ~ v1_funct_1(A_5236)
      | ~ v1_relat_1(A_5236)
      | r1_tarski(k2_relat_1(A_5236),B_5237) ) ),
    inference(resolution,[status(thm)],[c_6,c_28636])).

tff(c_29660,plain,(
    ! [B_5235,A_49,B_50,B_5237] :
      ( r2_hidden(B_5235,k2_relat_1('#skF_6'(A_49,B_5235)))
      | ~ v1_funct_1('#skF_6'(A_49,B_50))
      | ~ v1_relat_1('#skF_6'(A_49,B_50))
      | r1_tarski(k2_relat_1('#skF_6'(A_49,B_50)),B_5237) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_29215])).

tff(c_29903,plain,(
    ! [B_5308,A_5309,B_5310,B_5311] :
      ( r2_hidden(B_5308,k2_relat_1('#skF_6'(A_5309,B_5308)))
      | r1_tarski(k2_relat_1('#skF_6'(A_5309,B_5310)),B_5311) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_29660])).

tff(c_44,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_48,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_241,plain,(
    ! [A_112,C_113] :
      ( r2_hidden('#skF_5'(A_112,k2_relat_1(A_112),C_113),k1_relat_1(A_112))
      | ~ r2_hidden(C_113,k2_relat_1(A_112))
      | ~ v1_funct_1(A_112)
      | ~ v1_relat_1(A_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_248,plain,(
    ! [A_49,B_50,C_113] :
      ( r2_hidden('#skF_5'('#skF_6'(A_49,B_50),k2_relat_1('#skF_6'(A_49,B_50)),C_113),A_49)
      | ~ r2_hidden(C_113,k2_relat_1('#skF_6'(A_49,B_50)))
      | ~ v1_funct_1('#skF_6'(A_49,B_50))
      | ~ v1_relat_1('#skF_6'(A_49,B_50)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_241])).

tff(c_252,plain,(
    ! [A_49,B_50,C_113] :
      ( r2_hidden('#skF_5'('#skF_6'(A_49,B_50),k2_relat_1('#skF_6'(A_49,B_50)),C_113),A_49)
      | ~ r2_hidden(C_113,k2_relat_1('#skF_6'(A_49,B_50))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_248])).

tff(c_157,plain,(
    ! [A_94,C_95] :
      ( k1_funct_1(A_94,'#skF_5'(A_94,k2_relat_1(A_94),C_95)) = C_95
      | ~ r2_hidden(C_95,k2_relat_1(A_94))
      | ~ v1_funct_1(A_94)
      | ~ v1_relat_1(A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_174,plain,(
    ! [C_95,B_50,A_49] :
      ( C_95 = B_50
      | ~ r2_hidden(C_95,k2_relat_1('#skF_6'(A_49,B_50)))
      | ~ v1_funct_1('#skF_6'(A_49,B_50))
      | ~ v1_relat_1('#skF_6'(A_49,B_50))
      | ~ r2_hidden('#skF_5'('#skF_6'(A_49,B_50),k2_relat_1('#skF_6'(A_49,B_50)),C_95),A_49) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_157])).

tff(c_22132,plain,(
    ! [C_3716,B_3717,A_3718] :
      ( C_3716 = B_3717
      | ~ r2_hidden(C_3716,k2_relat_1('#skF_6'(A_3718,B_3717)))
      | ~ r2_hidden('#skF_5'('#skF_6'(A_3718,B_3717),k2_relat_1('#skF_6'(A_3718,B_3717)),C_3716),A_3718) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_174])).

tff(c_22137,plain,(
    ! [C_3719,B_3720,A_3721] :
      ( C_3719 = B_3720
      | ~ r2_hidden(C_3719,k2_relat_1('#skF_6'(A_3721,B_3720))) ) ),
    inference(resolution,[status(thm)],[c_252,c_22132])).

tff(c_22200,plain,(
    ! [A_3726,B_3727,B_3728] :
      ( '#skF_1'(k2_relat_1('#skF_6'(A_3726,B_3727)),B_3728) = B_3727
      | r1_tarski(k2_relat_1('#skF_6'(A_3726,B_3727)),B_3728) ) ),
    inference(resolution,[status(thm)],[c_6,c_22137])).

tff(c_42,plain,(
    ! [C_57] :
      ( ~ r1_tarski(k2_relat_1(C_57),'#skF_7')
      | k1_relat_1(C_57) != '#skF_8'
      | ~ v1_funct_1(C_57)
      | ~ v1_relat_1(C_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_22219,plain,(
    ! [A_3726,B_3727] :
      ( k1_relat_1('#skF_6'(A_3726,B_3727)) != '#skF_8'
      | ~ v1_funct_1('#skF_6'(A_3726,B_3727))
      | ~ v1_relat_1('#skF_6'(A_3726,B_3727))
      | '#skF_1'(k2_relat_1('#skF_6'(A_3726,B_3727)),'#skF_7') = B_3727 ) ),
    inference(resolution,[status(thm)],[c_22200,c_42])).

tff(c_22232,plain,(
    ! [A_3729,B_3730] :
      ( A_3729 != '#skF_8'
      | '#skF_1'(k2_relat_1('#skF_6'(A_3729,B_3730)),'#skF_7') = B_3730 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_22219])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_22280,plain,(
    ! [B_3734,A_3735] :
      ( ~ r2_hidden(B_3734,'#skF_7')
      | r1_tarski(k2_relat_1('#skF_6'(A_3735,B_3734)),'#skF_7')
      | A_3735 != '#skF_8' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22232,c_4])).

tff(c_22288,plain,(
    ! [A_3735,B_3734] :
      ( k1_relat_1('#skF_6'(A_3735,B_3734)) != '#skF_8'
      | ~ v1_funct_1('#skF_6'(A_3735,B_3734))
      | ~ v1_relat_1('#skF_6'(A_3735,B_3734))
      | ~ r2_hidden(B_3734,'#skF_7')
      | A_3735 != '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_22280,c_42])).

tff(c_22295,plain,(
    ! [B_3734,A_3735] :
      ( ~ r2_hidden(B_3734,'#skF_7')
      | A_3735 != '#skF_8' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_22288])).

tff(c_22297,plain,(
    ! [A_3735] : A_3735 != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_22295])).

tff(c_22301,plain,(
    $false ),
    inference(reflexivity,[status(thm),theory(equality)],[c_22297])).

tff(c_22303,plain,(
    ! [B_3736] : ~ r2_hidden(B_3736,'#skF_7') ),
    inference(splitRight,[status(thm)],[c_22295])).

tff(c_22338,plain,(
    ! [B_3737] : r1_tarski('#skF_7',B_3737) ),
    inference(resolution,[status(thm)],[c_6,c_22303])).

tff(c_14,plain,(
    ! [A_8] : r1_tarski(k1_xboole_0,A_8) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_61,plain,(
    ! [B_68,A_69] :
      ( B_68 = A_69
      | ~ r1_tarski(B_68,A_69)
      | ~ r1_tarski(A_69,B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_70,plain,(
    ! [A_8] :
      ( k1_xboole_0 = A_8
      | ~ r1_tarski(A_8,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_14,c_61])).

tff(c_22350,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_22338,c_70])).

tff(c_22361,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_22350])).

tff(c_22362,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_22363,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_22369,plain,(
    '#skF_7' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22362,c_22363])).

tff(c_22374,plain,(
    ! [C_57] :
      ( ~ r1_tarski(k2_relat_1(C_57),'#skF_8')
      | k1_relat_1(C_57) != '#skF_8'
      | ~ v1_funct_1(C_57)
      | ~ v1_relat_1(C_57) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22369,c_42])).

tff(c_29941,plain,(
    ! [A_5309,B_5310,B_5308] :
      ( k1_relat_1('#skF_6'(A_5309,B_5310)) != '#skF_8'
      | ~ v1_funct_1('#skF_6'(A_5309,B_5310))
      | ~ v1_relat_1('#skF_6'(A_5309,B_5310))
      | r2_hidden(B_5308,k2_relat_1('#skF_6'(A_5309,B_5308))) ) ),
    inference(resolution,[status(thm)],[c_29903,c_22374])).

tff(c_30368,plain,(
    ! [A_5309,B_5308] :
      ( A_5309 != '#skF_8'
      | r2_hidden(B_5308,k2_relat_1('#skF_6'(A_5309,B_5308))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_29941])).

tff(c_22491,plain,(
    ! [A_49,B_50,C_3774] :
      ( r2_hidden('#skF_5'('#skF_6'(A_49,B_50),k2_relat_1('#skF_6'(A_49,B_50)),C_3774),A_49)
      | ~ r2_hidden(C_3774,k2_relat_1('#skF_6'(A_49,B_50)))
      | ~ v1_funct_1('#skF_6'(A_49,B_50))
      | ~ v1_relat_1('#skF_6'(A_49,B_50)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_22484])).

tff(c_37986,plain,(
    ! [A_6321,B_6322,C_6323] :
      ( r2_hidden('#skF_5'('#skF_6'(A_6321,B_6322),k2_relat_1('#skF_6'(A_6321,B_6322)),C_6323),A_6321)
      | ~ r2_hidden(C_6323,k2_relat_1('#skF_6'(A_6321,B_6322))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_22491])).

tff(c_22364,plain,(
    ! [A_8] : r1_tarski('#skF_8',A_8) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22362,c_14])).

tff(c_22396,plain,(
    ! [B_3750,A_3751] :
      ( B_3750 = A_3751
      | ~ r1_tarski(B_3750,A_3751)
      | ~ r1_tarski(A_3751,B_3750) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_22401,plain,(
    ! [A_8] :
      ( A_8 = '#skF_8'
      | ~ r1_tarski(A_8,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_22364,c_22396])).

tff(c_30589,plain,(
    ! [A_5382,B_5383,B_5384] :
      ( k2_relat_1('#skF_6'(A_5382,B_5383)) = '#skF_8'
      | r2_hidden(B_5384,k2_relat_1('#skF_6'(A_5382,B_5384))) ) ),
    inference(resolution,[status(thm)],[c_29903,c_22401])).

tff(c_22492,plain,(
    ! [B_50,A_3773,C_3774] :
      ( r2_hidden(B_50,k2_relat_1('#skF_6'(k1_relat_1(A_3773),B_50)))
      | ~ r2_hidden(C_3774,k2_relat_1(A_3773))
      | ~ v1_funct_1(A_3773)
      | ~ v1_relat_1(A_3773) ) ),
    inference(resolution,[status(thm)],[c_22484,c_22449])).

tff(c_30623,plain,(
    ! [A_5382,B_5383,B_50,B_5384,C_3774] :
      ( r2_hidden(B_50,k2_relat_1('#skF_6'(k1_relat_1('#skF_6'(A_5382,B_5383)),B_50)))
      | ~ r2_hidden(C_3774,'#skF_8')
      | ~ v1_funct_1('#skF_6'(A_5382,B_5383))
      | ~ v1_relat_1('#skF_6'(A_5382,B_5383))
      | r2_hidden(B_5384,k2_relat_1('#skF_6'(A_5382,B_5384))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30589,c_22492])).

tff(c_31138,plain,(
    ! [B_50,A_5382,C_3774,B_5384] :
      ( r2_hidden(B_50,k2_relat_1('#skF_6'(A_5382,B_50)))
      | ~ r2_hidden(C_3774,'#skF_8')
      | r2_hidden(B_5384,k2_relat_1('#skF_6'(A_5382,B_5384))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_30623])).

tff(c_36271,plain,(
    ! [C_3774] : ~ r2_hidden(C_3774,'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_31138])).

tff(c_38428,plain,(
    ! [C_6358,B_6359] : ~ r2_hidden(C_6358,k2_relat_1('#skF_6'('#skF_8',B_6359))) ),
    inference(resolution,[status(thm)],[c_37986,c_36271])).

tff(c_38517,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_30368,c_38428])).

tff(c_38518,plain,(
    ! [B_50,A_5382,B_5384] :
      ( r2_hidden(B_50,k2_relat_1('#skF_6'(A_5382,B_50)))
      | r2_hidden(B_5384,k2_relat_1('#skF_6'(A_5382,B_5384))) ) ),
    inference(splitRight,[status(thm)],[c_31138])).

tff(c_38531,plain,(
    ! [B_50,A_5382] : r2_hidden(B_50,k2_relat_1('#skF_6'(A_5382,B_50))) ),
    inference(factorization,[status(thm),theory(equality)],[c_38518])).

tff(c_22495,plain,(
    ! [A_49,B_50,C_3774] :
      ( r2_hidden('#skF_5'('#skF_6'(A_49,B_50),k2_relat_1('#skF_6'(A_49,B_50)),C_3774),A_49)
      | ~ r2_hidden(C_3774,k2_relat_1('#skF_6'(A_49,B_50))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_22491])).

tff(c_22521,plain,(
    ! [A_3783,C_3784] :
      ( k1_funct_1(A_3783,'#skF_5'(A_3783,k2_relat_1(A_3783),C_3784)) = C_3784
      | ~ r2_hidden(C_3784,k2_relat_1(A_3783))
      | ~ v1_funct_1(A_3783)
      | ~ v1_relat_1(A_3783) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_22538,plain,(
    ! [C_3784,B_50,A_49] :
      ( C_3784 = B_50
      | ~ r2_hidden(C_3784,k2_relat_1('#skF_6'(A_49,B_50)))
      | ~ v1_funct_1('#skF_6'(A_49,B_50))
      | ~ v1_relat_1('#skF_6'(A_49,B_50))
      | ~ r2_hidden('#skF_5'('#skF_6'(A_49,B_50),k2_relat_1('#skF_6'(A_49,B_50)),C_3784),A_49) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_22521])).

tff(c_39060,plain,(
    ! [C_6445,B_6446,A_6447] :
      ( C_6445 = B_6446
      | ~ r2_hidden(C_6445,k2_relat_1('#skF_6'(A_6447,B_6446)))
      | ~ r2_hidden('#skF_5'('#skF_6'(A_6447,B_6446),k2_relat_1('#skF_6'(A_6447,B_6446)),C_6445),A_6447) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_22538])).

tff(c_39065,plain,(
    ! [C_6448,B_6449,A_6450] :
      ( C_6448 = B_6449
      | ~ r2_hidden(C_6448,k2_relat_1('#skF_6'(A_6450,B_6449))) ) ),
    inference(resolution,[status(thm)],[c_22495,c_39060])).

tff(c_39118,plain,(
    ! [A_6455,B_6456,B_6457] :
      ( '#skF_1'(k2_relat_1('#skF_6'(A_6455,B_6456)),B_6457) = B_6456
      | r1_tarski(k2_relat_1('#skF_6'(A_6455,B_6456)),B_6457) ) ),
    inference(resolution,[status(thm)],[c_6,c_39065])).

tff(c_39139,plain,(
    ! [A_6455,B_6456] :
      ( k1_relat_1('#skF_6'(A_6455,B_6456)) != '#skF_8'
      | ~ v1_funct_1('#skF_6'(A_6455,B_6456))
      | ~ v1_relat_1('#skF_6'(A_6455,B_6456))
      | '#skF_1'(k2_relat_1('#skF_6'(A_6455,B_6456)),'#skF_8') = B_6456 ) ),
    inference(resolution,[status(thm)],[c_39118,c_22374])).

tff(c_39150,plain,(
    ! [A_6458,B_6459] :
      ( A_6458 != '#skF_8'
      | '#skF_1'(k2_relat_1('#skF_6'(A_6458,B_6459)),'#skF_8') = B_6459 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_39139])).

tff(c_39198,plain,(
    ! [B_6463,A_6464] :
      ( ~ r2_hidden(B_6463,'#skF_8')
      | r1_tarski(k2_relat_1('#skF_6'(A_6464,B_6463)),'#skF_8')
      | A_6464 != '#skF_8' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_39150,c_4])).

tff(c_39213,plain,(
    ! [A_6464,B_6463] :
      ( k1_relat_1('#skF_6'(A_6464,B_6463)) != '#skF_8'
      | ~ v1_funct_1('#skF_6'(A_6464,B_6463))
      | ~ v1_relat_1('#skF_6'(A_6464,B_6463))
      | ~ r2_hidden(B_6463,'#skF_8')
      | A_6464 != '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_39198,c_22374])).

tff(c_39223,plain,(
    ! [B_6463,A_6464] :
      ( ~ r2_hidden(B_6463,'#skF_8')
      | A_6464 != '#skF_8' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_39213])).

tff(c_39224,plain,(
    ! [A_6464] : A_6464 != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_39223])).

tff(c_39228,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_39224,c_22369])).

tff(c_39230,plain,(
    ! [B_6465] : ~ r2_hidden(B_6465,'#skF_8') ),
    inference(splitRight,[status(thm)],[c_39223])).

tff(c_39273,plain,(
    ! [C_6469,B_6470] : ~ r2_hidden(C_6469,k2_relat_1('#skF_6'('#skF_8',B_6470))) ),
    inference(resolution,[status(thm)],[c_22495,c_39230])).

tff(c_39313,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_38531,c_39273])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 09:22:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.92/4.16  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.99/4.17  
% 11.99/4.17  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.99/4.17  %$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_7 > #skF_3 > #skF_5 > #skF_8 > #skF_2 > #skF_1 > #skF_4
% 11.99/4.17  
% 11.99/4.17  %Foreground sorts:
% 11.99/4.17  
% 11.99/4.17  
% 11.99/4.17  %Background operators:
% 11.99/4.17  
% 11.99/4.17  
% 11.99/4.17  %Foreground operators:
% 11.99/4.17  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 11.99/4.17  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 11.99/4.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.99/4.17  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 11.99/4.17  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.99/4.17  tff('#skF_7', type, '#skF_7': $i).
% 11.99/4.17  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 11.99/4.17  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.99/4.17  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 11.99/4.17  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 11.99/4.17  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 11.99/4.17  tff('#skF_8', type, '#skF_8': $i).
% 11.99/4.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.99/4.17  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 11.99/4.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.99/4.17  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 11.99/4.17  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 11.99/4.17  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 11.99/4.17  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 11.99/4.17  
% 11.99/4.19  tff(f_67, axiom, (![A, B]: (?[C]: (((v1_relat_1(C) & v1_funct_1(C)) & (k1_relat_1(C) = A)) & (![D]: (r2_hidden(D, A) => (k1_funct_1(C, D) = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', s3_funct_1__e2_24__funct_1)).
% 11.99/4.19  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 11.99/4.19  tff(f_55, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_funct_1)).
% 11.99/4.19  tff(f_85, negated_conjecture, ~(![A, B]: ~(~((A = k1_xboole_0) & ~(B = k1_xboole_0)) & (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => ~((B = k1_relat_1(C)) & r1_tarski(k2_relat_1(C), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_funct_1)).
% 11.99/4.19  tff(f_40, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 11.99/4.19  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 11.99/4.19  tff(c_40, plain, (![A_49, B_50]: (v1_relat_1('#skF_6'(A_49, B_50)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 11.99/4.19  tff(c_38, plain, (![A_49, B_50]: (v1_funct_1('#skF_6'(A_49, B_50)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 11.99/4.19  tff(c_36, plain, (![A_49, B_50]: (k1_relat_1('#skF_6'(A_49, B_50))=A_49)), inference(cnfTransformation, [status(thm)], [f_67])).
% 11.99/4.19  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 11.99/4.19  tff(c_22484, plain, (![A_3773, C_3774]: (r2_hidden('#skF_5'(A_3773, k2_relat_1(A_3773), C_3774), k1_relat_1(A_3773)) | ~r2_hidden(C_3774, k2_relat_1(A_3773)) | ~v1_funct_1(A_3773) | ~v1_relat_1(A_3773))), inference(cnfTransformation, [status(thm)], [f_55])).
% 11.99/4.19  tff(c_34, plain, (![A_49, B_50, D_55]: (k1_funct_1('#skF_6'(A_49, B_50), D_55)=B_50 | ~r2_hidden(D_55, A_49))), inference(cnfTransformation, [status(thm)], [f_67])).
% 11.99/4.19  tff(c_22441, plain, (![A_3762, D_3763]: (r2_hidden(k1_funct_1(A_3762, D_3763), k2_relat_1(A_3762)) | ~r2_hidden(D_3763, k1_relat_1(A_3762)) | ~v1_funct_1(A_3762) | ~v1_relat_1(A_3762))), inference(cnfTransformation, [status(thm)], [f_55])).
% 11.99/4.19  tff(c_22446, plain, (![B_50, A_49, D_55]: (r2_hidden(B_50, k2_relat_1('#skF_6'(A_49, B_50))) | ~r2_hidden(D_55, k1_relat_1('#skF_6'(A_49, B_50))) | ~v1_funct_1('#skF_6'(A_49, B_50)) | ~v1_relat_1('#skF_6'(A_49, B_50)) | ~r2_hidden(D_55, A_49))), inference(superposition, [status(thm), theory('equality')], [c_34, c_22441])).
% 11.99/4.19  tff(c_22449, plain, (![B_50, A_49, D_55]: (r2_hidden(B_50, k2_relat_1('#skF_6'(A_49, B_50))) | ~r2_hidden(D_55, A_49))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_36, c_22446])).
% 11.99/4.19  tff(c_28636, plain, (![B_5161, A_5162, C_5163]: (r2_hidden(B_5161, k2_relat_1('#skF_6'(k1_relat_1(A_5162), B_5161))) | ~r2_hidden(C_5163, k2_relat_1(A_5162)) | ~v1_funct_1(A_5162) | ~v1_relat_1(A_5162))), inference(resolution, [status(thm)], [c_22484, c_22449])).
% 11.99/4.19  tff(c_29215, plain, (![B_5235, A_5236, B_5237]: (r2_hidden(B_5235, k2_relat_1('#skF_6'(k1_relat_1(A_5236), B_5235))) | ~v1_funct_1(A_5236) | ~v1_relat_1(A_5236) | r1_tarski(k2_relat_1(A_5236), B_5237))), inference(resolution, [status(thm)], [c_6, c_28636])).
% 11.99/4.19  tff(c_29660, plain, (![B_5235, A_49, B_50, B_5237]: (r2_hidden(B_5235, k2_relat_1('#skF_6'(A_49, B_5235))) | ~v1_funct_1('#skF_6'(A_49, B_50)) | ~v1_relat_1('#skF_6'(A_49, B_50)) | r1_tarski(k2_relat_1('#skF_6'(A_49, B_50)), B_5237))), inference(superposition, [status(thm), theory('equality')], [c_36, c_29215])).
% 11.99/4.19  tff(c_29903, plain, (![B_5308, A_5309, B_5310, B_5311]: (r2_hidden(B_5308, k2_relat_1('#skF_6'(A_5309, B_5308))) | r1_tarski(k2_relat_1('#skF_6'(A_5309, B_5310)), B_5311))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_29660])).
% 11.99/4.19  tff(c_44, plain, (k1_xboole_0='#skF_8' | k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_85])).
% 11.99/4.19  tff(c_48, plain, (k1_xboole_0!='#skF_7'), inference(splitLeft, [status(thm)], [c_44])).
% 11.99/4.19  tff(c_241, plain, (![A_112, C_113]: (r2_hidden('#skF_5'(A_112, k2_relat_1(A_112), C_113), k1_relat_1(A_112)) | ~r2_hidden(C_113, k2_relat_1(A_112)) | ~v1_funct_1(A_112) | ~v1_relat_1(A_112))), inference(cnfTransformation, [status(thm)], [f_55])).
% 11.99/4.19  tff(c_248, plain, (![A_49, B_50, C_113]: (r2_hidden('#skF_5'('#skF_6'(A_49, B_50), k2_relat_1('#skF_6'(A_49, B_50)), C_113), A_49) | ~r2_hidden(C_113, k2_relat_1('#skF_6'(A_49, B_50))) | ~v1_funct_1('#skF_6'(A_49, B_50)) | ~v1_relat_1('#skF_6'(A_49, B_50)))), inference(superposition, [status(thm), theory('equality')], [c_36, c_241])).
% 11.99/4.19  tff(c_252, plain, (![A_49, B_50, C_113]: (r2_hidden('#skF_5'('#skF_6'(A_49, B_50), k2_relat_1('#skF_6'(A_49, B_50)), C_113), A_49) | ~r2_hidden(C_113, k2_relat_1('#skF_6'(A_49, B_50))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_248])).
% 11.99/4.19  tff(c_157, plain, (![A_94, C_95]: (k1_funct_1(A_94, '#skF_5'(A_94, k2_relat_1(A_94), C_95))=C_95 | ~r2_hidden(C_95, k2_relat_1(A_94)) | ~v1_funct_1(A_94) | ~v1_relat_1(A_94))), inference(cnfTransformation, [status(thm)], [f_55])).
% 11.99/4.19  tff(c_174, plain, (![C_95, B_50, A_49]: (C_95=B_50 | ~r2_hidden(C_95, k2_relat_1('#skF_6'(A_49, B_50))) | ~v1_funct_1('#skF_6'(A_49, B_50)) | ~v1_relat_1('#skF_6'(A_49, B_50)) | ~r2_hidden('#skF_5'('#skF_6'(A_49, B_50), k2_relat_1('#skF_6'(A_49, B_50)), C_95), A_49))), inference(superposition, [status(thm), theory('equality')], [c_34, c_157])).
% 11.99/4.19  tff(c_22132, plain, (![C_3716, B_3717, A_3718]: (C_3716=B_3717 | ~r2_hidden(C_3716, k2_relat_1('#skF_6'(A_3718, B_3717))) | ~r2_hidden('#skF_5'('#skF_6'(A_3718, B_3717), k2_relat_1('#skF_6'(A_3718, B_3717)), C_3716), A_3718))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_174])).
% 11.99/4.19  tff(c_22137, plain, (![C_3719, B_3720, A_3721]: (C_3719=B_3720 | ~r2_hidden(C_3719, k2_relat_1('#skF_6'(A_3721, B_3720))))), inference(resolution, [status(thm)], [c_252, c_22132])).
% 11.99/4.19  tff(c_22200, plain, (![A_3726, B_3727, B_3728]: ('#skF_1'(k2_relat_1('#skF_6'(A_3726, B_3727)), B_3728)=B_3727 | r1_tarski(k2_relat_1('#skF_6'(A_3726, B_3727)), B_3728))), inference(resolution, [status(thm)], [c_6, c_22137])).
% 11.99/4.19  tff(c_42, plain, (![C_57]: (~r1_tarski(k2_relat_1(C_57), '#skF_7') | k1_relat_1(C_57)!='#skF_8' | ~v1_funct_1(C_57) | ~v1_relat_1(C_57))), inference(cnfTransformation, [status(thm)], [f_85])).
% 11.99/4.19  tff(c_22219, plain, (![A_3726, B_3727]: (k1_relat_1('#skF_6'(A_3726, B_3727))!='#skF_8' | ~v1_funct_1('#skF_6'(A_3726, B_3727)) | ~v1_relat_1('#skF_6'(A_3726, B_3727)) | '#skF_1'(k2_relat_1('#skF_6'(A_3726, B_3727)), '#skF_7')=B_3727)), inference(resolution, [status(thm)], [c_22200, c_42])).
% 11.99/4.19  tff(c_22232, plain, (![A_3729, B_3730]: (A_3729!='#skF_8' | '#skF_1'(k2_relat_1('#skF_6'(A_3729, B_3730)), '#skF_7')=B_3730)), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_36, c_22219])).
% 11.99/4.19  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 11.99/4.19  tff(c_22280, plain, (![B_3734, A_3735]: (~r2_hidden(B_3734, '#skF_7') | r1_tarski(k2_relat_1('#skF_6'(A_3735, B_3734)), '#skF_7') | A_3735!='#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_22232, c_4])).
% 11.99/4.19  tff(c_22288, plain, (![A_3735, B_3734]: (k1_relat_1('#skF_6'(A_3735, B_3734))!='#skF_8' | ~v1_funct_1('#skF_6'(A_3735, B_3734)) | ~v1_relat_1('#skF_6'(A_3735, B_3734)) | ~r2_hidden(B_3734, '#skF_7') | A_3735!='#skF_8')), inference(resolution, [status(thm)], [c_22280, c_42])).
% 11.99/4.19  tff(c_22295, plain, (![B_3734, A_3735]: (~r2_hidden(B_3734, '#skF_7') | A_3735!='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_36, c_22288])).
% 11.99/4.19  tff(c_22297, plain, (![A_3735]: (A_3735!='#skF_8')), inference(splitLeft, [status(thm)], [c_22295])).
% 11.99/4.19  tff(c_22301, plain, $false, inference(reflexivity, [status(thm), theory('equality')], [c_22297])).
% 11.99/4.19  tff(c_22303, plain, (![B_3736]: (~r2_hidden(B_3736, '#skF_7'))), inference(splitRight, [status(thm)], [c_22295])).
% 11.99/4.19  tff(c_22338, plain, (![B_3737]: (r1_tarski('#skF_7', B_3737))), inference(resolution, [status(thm)], [c_6, c_22303])).
% 11.99/4.19  tff(c_14, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 11.99/4.19  tff(c_61, plain, (![B_68, A_69]: (B_68=A_69 | ~r1_tarski(B_68, A_69) | ~r1_tarski(A_69, B_68))), inference(cnfTransformation, [status(thm)], [f_38])).
% 11.99/4.19  tff(c_70, plain, (![A_8]: (k1_xboole_0=A_8 | ~r1_tarski(A_8, k1_xboole_0))), inference(resolution, [status(thm)], [c_14, c_61])).
% 11.99/4.19  tff(c_22350, plain, (k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_22338, c_70])).
% 11.99/4.19  tff(c_22361, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_22350])).
% 11.99/4.19  tff(c_22362, plain, (k1_xboole_0='#skF_8'), inference(splitRight, [status(thm)], [c_44])).
% 11.99/4.19  tff(c_22363, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_44])).
% 11.99/4.19  tff(c_22369, plain, ('#skF_7'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_22362, c_22363])).
% 11.99/4.19  tff(c_22374, plain, (![C_57]: (~r1_tarski(k2_relat_1(C_57), '#skF_8') | k1_relat_1(C_57)!='#skF_8' | ~v1_funct_1(C_57) | ~v1_relat_1(C_57))), inference(demodulation, [status(thm), theory('equality')], [c_22369, c_42])).
% 11.99/4.19  tff(c_29941, plain, (![A_5309, B_5310, B_5308]: (k1_relat_1('#skF_6'(A_5309, B_5310))!='#skF_8' | ~v1_funct_1('#skF_6'(A_5309, B_5310)) | ~v1_relat_1('#skF_6'(A_5309, B_5310)) | r2_hidden(B_5308, k2_relat_1('#skF_6'(A_5309, B_5308))))), inference(resolution, [status(thm)], [c_29903, c_22374])).
% 11.99/4.19  tff(c_30368, plain, (![A_5309, B_5308]: (A_5309!='#skF_8' | r2_hidden(B_5308, k2_relat_1('#skF_6'(A_5309, B_5308))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_36, c_29941])).
% 11.99/4.19  tff(c_22491, plain, (![A_49, B_50, C_3774]: (r2_hidden('#skF_5'('#skF_6'(A_49, B_50), k2_relat_1('#skF_6'(A_49, B_50)), C_3774), A_49) | ~r2_hidden(C_3774, k2_relat_1('#skF_6'(A_49, B_50))) | ~v1_funct_1('#skF_6'(A_49, B_50)) | ~v1_relat_1('#skF_6'(A_49, B_50)))), inference(superposition, [status(thm), theory('equality')], [c_36, c_22484])).
% 11.99/4.19  tff(c_37986, plain, (![A_6321, B_6322, C_6323]: (r2_hidden('#skF_5'('#skF_6'(A_6321, B_6322), k2_relat_1('#skF_6'(A_6321, B_6322)), C_6323), A_6321) | ~r2_hidden(C_6323, k2_relat_1('#skF_6'(A_6321, B_6322))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_22491])).
% 11.99/4.19  tff(c_22364, plain, (![A_8]: (r1_tarski('#skF_8', A_8))), inference(demodulation, [status(thm), theory('equality')], [c_22362, c_14])).
% 11.99/4.19  tff(c_22396, plain, (![B_3750, A_3751]: (B_3750=A_3751 | ~r1_tarski(B_3750, A_3751) | ~r1_tarski(A_3751, B_3750))), inference(cnfTransformation, [status(thm)], [f_38])).
% 11.99/4.19  tff(c_22401, plain, (![A_8]: (A_8='#skF_8' | ~r1_tarski(A_8, '#skF_8'))), inference(resolution, [status(thm)], [c_22364, c_22396])).
% 11.99/4.19  tff(c_30589, plain, (![A_5382, B_5383, B_5384]: (k2_relat_1('#skF_6'(A_5382, B_5383))='#skF_8' | r2_hidden(B_5384, k2_relat_1('#skF_6'(A_5382, B_5384))))), inference(resolution, [status(thm)], [c_29903, c_22401])).
% 11.99/4.19  tff(c_22492, plain, (![B_50, A_3773, C_3774]: (r2_hidden(B_50, k2_relat_1('#skF_6'(k1_relat_1(A_3773), B_50))) | ~r2_hidden(C_3774, k2_relat_1(A_3773)) | ~v1_funct_1(A_3773) | ~v1_relat_1(A_3773))), inference(resolution, [status(thm)], [c_22484, c_22449])).
% 11.99/4.19  tff(c_30623, plain, (![A_5382, B_5383, B_50, B_5384, C_3774]: (r2_hidden(B_50, k2_relat_1('#skF_6'(k1_relat_1('#skF_6'(A_5382, B_5383)), B_50))) | ~r2_hidden(C_3774, '#skF_8') | ~v1_funct_1('#skF_6'(A_5382, B_5383)) | ~v1_relat_1('#skF_6'(A_5382, B_5383)) | r2_hidden(B_5384, k2_relat_1('#skF_6'(A_5382, B_5384))))), inference(superposition, [status(thm), theory('equality')], [c_30589, c_22492])).
% 11.99/4.19  tff(c_31138, plain, (![B_50, A_5382, C_3774, B_5384]: (r2_hidden(B_50, k2_relat_1('#skF_6'(A_5382, B_50))) | ~r2_hidden(C_3774, '#skF_8') | r2_hidden(B_5384, k2_relat_1('#skF_6'(A_5382, B_5384))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_36, c_30623])).
% 11.99/4.19  tff(c_36271, plain, (![C_3774]: (~r2_hidden(C_3774, '#skF_8'))), inference(splitLeft, [status(thm)], [c_31138])).
% 11.99/4.19  tff(c_38428, plain, (![C_6358, B_6359]: (~r2_hidden(C_6358, k2_relat_1('#skF_6'('#skF_8', B_6359))))), inference(resolution, [status(thm)], [c_37986, c_36271])).
% 11.99/4.19  tff(c_38517, plain, $false, inference(resolution, [status(thm)], [c_30368, c_38428])).
% 11.99/4.19  tff(c_38518, plain, (![B_50, A_5382, B_5384]: (r2_hidden(B_50, k2_relat_1('#skF_6'(A_5382, B_50))) | r2_hidden(B_5384, k2_relat_1('#skF_6'(A_5382, B_5384))))), inference(splitRight, [status(thm)], [c_31138])).
% 11.99/4.19  tff(c_38531, plain, (![B_50, A_5382]: (r2_hidden(B_50, k2_relat_1('#skF_6'(A_5382, B_50))))), inference(factorization, [status(thm), theory('equality')], [c_38518])).
% 11.99/4.19  tff(c_22495, plain, (![A_49, B_50, C_3774]: (r2_hidden('#skF_5'('#skF_6'(A_49, B_50), k2_relat_1('#skF_6'(A_49, B_50)), C_3774), A_49) | ~r2_hidden(C_3774, k2_relat_1('#skF_6'(A_49, B_50))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_22491])).
% 11.99/4.19  tff(c_22521, plain, (![A_3783, C_3784]: (k1_funct_1(A_3783, '#skF_5'(A_3783, k2_relat_1(A_3783), C_3784))=C_3784 | ~r2_hidden(C_3784, k2_relat_1(A_3783)) | ~v1_funct_1(A_3783) | ~v1_relat_1(A_3783))), inference(cnfTransformation, [status(thm)], [f_55])).
% 11.99/4.19  tff(c_22538, plain, (![C_3784, B_50, A_49]: (C_3784=B_50 | ~r2_hidden(C_3784, k2_relat_1('#skF_6'(A_49, B_50))) | ~v1_funct_1('#skF_6'(A_49, B_50)) | ~v1_relat_1('#skF_6'(A_49, B_50)) | ~r2_hidden('#skF_5'('#skF_6'(A_49, B_50), k2_relat_1('#skF_6'(A_49, B_50)), C_3784), A_49))), inference(superposition, [status(thm), theory('equality')], [c_34, c_22521])).
% 11.99/4.19  tff(c_39060, plain, (![C_6445, B_6446, A_6447]: (C_6445=B_6446 | ~r2_hidden(C_6445, k2_relat_1('#skF_6'(A_6447, B_6446))) | ~r2_hidden('#skF_5'('#skF_6'(A_6447, B_6446), k2_relat_1('#skF_6'(A_6447, B_6446)), C_6445), A_6447))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_22538])).
% 11.99/4.19  tff(c_39065, plain, (![C_6448, B_6449, A_6450]: (C_6448=B_6449 | ~r2_hidden(C_6448, k2_relat_1('#skF_6'(A_6450, B_6449))))), inference(resolution, [status(thm)], [c_22495, c_39060])).
% 11.99/4.19  tff(c_39118, plain, (![A_6455, B_6456, B_6457]: ('#skF_1'(k2_relat_1('#skF_6'(A_6455, B_6456)), B_6457)=B_6456 | r1_tarski(k2_relat_1('#skF_6'(A_6455, B_6456)), B_6457))), inference(resolution, [status(thm)], [c_6, c_39065])).
% 11.99/4.19  tff(c_39139, plain, (![A_6455, B_6456]: (k1_relat_1('#skF_6'(A_6455, B_6456))!='#skF_8' | ~v1_funct_1('#skF_6'(A_6455, B_6456)) | ~v1_relat_1('#skF_6'(A_6455, B_6456)) | '#skF_1'(k2_relat_1('#skF_6'(A_6455, B_6456)), '#skF_8')=B_6456)), inference(resolution, [status(thm)], [c_39118, c_22374])).
% 11.99/4.19  tff(c_39150, plain, (![A_6458, B_6459]: (A_6458!='#skF_8' | '#skF_1'(k2_relat_1('#skF_6'(A_6458, B_6459)), '#skF_8')=B_6459)), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_36, c_39139])).
% 11.99/4.19  tff(c_39198, plain, (![B_6463, A_6464]: (~r2_hidden(B_6463, '#skF_8') | r1_tarski(k2_relat_1('#skF_6'(A_6464, B_6463)), '#skF_8') | A_6464!='#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_39150, c_4])).
% 11.99/4.19  tff(c_39213, plain, (![A_6464, B_6463]: (k1_relat_1('#skF_6'(A_6464, B_6463))!='#skF_8' | ~v1_funct_1('#skF_6'(A_6464, B_6463)) | ~v1_relat_1('#skF_6'(A_6464, B_6463)) | ~r2_hidden(B_6463, '#skF_8') | A_6464!='#skF_8')), inference(resolution, [status(thm)], [c_39198, c_22374])).
% 11.99/4.19  tff(c_39223, plain, (![B_6463, A_6464]: (~r2_hidden(B_6463, '#skF_8') | A_6464!='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_36, c_39213])).
% 11.99/4.19  tff(c_39224, plain, (![A_6464]: (A_6464!='#skF_8')), inference(splitLeft, [status(thm)], [c_39223])).
% 11.99/4.19  tff(c_39228, plain, $false, inference(negUnitSimplification, [status(thm)], [c_39224, c_22369])).
% 11.99/4.19  tff(c_39230, plain, (![B_6465]: (~r2_hidden(B_6465, '#skF_8'))), inference(splitRight, [status(thm)], [c_39223])).
% 11.99/4.19  tff(c_39273, plain, (![C_6469, B_6470]: (~r2_hidden(C_6469, k2_relat_1('#skF_6'('#skF_8', B_6470))))), inference(resolution, [status(thm)], [c_22495, c_39230])).
% 11.99/4.19  tff(c_39313, plain, $false, inference(resolution, [status(thm)], [c_38531, c_39273])).
% 11.99/4.19  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.99/4.19  
% 11.99/4.19  Inference rules
% 11.99/4.19  ----------------------
% 11.99/4.19  #Ref     : 2
% 11.99/4.19  #Sup     : 6734
% 11.99/4.19  #Fact    : 8
% 11.99/4.19  #Define  : 0
% 11.99/4.19  #Split   : 8
% 11.99/4.19  #Chain   : 0
% 11.99/4.19  #Close   : 0
% 11.99/4.19  
% 11.99/4.19  Ordering : KBO
% 11.99/4.19  
% 11.99/4.19  Simplification rules
% 11.99/4.19  ----------------------
% 11.99/4.19  #Subsume      : 2004
% 11.99/4.19  #Demod        : 976
% 11.99/4.19  #Tautology    : 284
% 11.99/4.19  #SimpNegUnit  : 72
% 11.99/4.19  #BackRed      : 5
% 11.99/4.19  
% 11.99/4.19  #Partial instantiations: 4104
% 11.99/4.19  #Strategies tried      : 1
% 11.99/4.19  
% 11.99/4.19  Timing (in seconds)
% 11.99/4.19  ----------------------
% 11.99/4.20  Preprocessing        : 0.39
% 11.99/4.20  Parsing              : 0.20
% 11.99/4.20  CNF conversion       : 0.03
% 11.99/4.20  Main loop            : 3.02
% 11.99/4.20  Inferencing          : 0.97
% 11.99/4.20  Reduction            : 0.81
% 11.99/4.20  Demodulation         : 0.60
% 11.99/4.20  BG Simplification    : 0.14
% 11.99/4.20  Subsumption          : 0.89
% 11.99/4.20  Abstraction          : 0.14
% 11.99/4.20  MUC search           : 0.00
% 11.99/4.20  Cooper               : 0.00
% 11.99/4.20  Total                : 3.45
% 11.99/4.20  Index Insertion      : 0.00
% 11.99/4.20  Index Deletion       : 0.00
% 11.99/4.20  Index Matching       : 0.00
% 11.99/4.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
