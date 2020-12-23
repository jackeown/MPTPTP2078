%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:02 EST 2020

% Result     : Theorem 14.85s
% Output     : CNFRefutation 14.98s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 204 expanded)
%              Number of leaves         :   24 (  92 expanded)
%              Depth                    :   17
%              Number of atoms          :  224 (1033 expanded)
%              Number of equality atoms :   53 ( 394 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k5_relat_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_4 > #skF_7 > #skF_3 > #skF_6 > #skF_9 > #skF_8 > #skF_2 > #skF_1 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

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

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_111,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ! [C] :
            ( ( v1_relat_1(C)
              & v1_funct_1(C) )
           => ! [D] :
                ( ( v1_relat_1(D)
                  & v1_funct_1(D) )
               => ( ( A = k2_relat_1(B)
                    & k1_relat_1(C) = A
                    & k1_relat_1(D) = A
                    & k5_relat_1(B,C) = k5_relat_1(B,D) )
                 => C = D ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t156_funct_1)).

tff(f_86,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( k1_relat_1(A) = k1_relat_1(B)
              & ! [C] :
                  ( r2_hidden(C,k1_relat_1(A))
                 => k1_funct_1(A,C) = k1_funct_1(B,C) ) )
           => A = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_funct_1)).

tff(f_40,axiom,(
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

tff(f_55,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ( r2_hidden(A,k1_relat_1(k5_relat_1(C,B)))
          <=> ( r2_hidden(A,k1_relat_1(C))
              & r2_hidden(k1_funct_1(C,A),k1_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_funct_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ( r2_hidden(A,k1_relat_1(k5_relat_1(C,B)))
           => k1_funct_1(k5_relat_1(C,B),A) = k1_funct_1(B,k1_funct_1(C,A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_funct_1)).

tff(c_32,plain,(
    '#skF_9' != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_44,plain,(
    v1_relat_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_42,plain,(
    v1_funct_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_36,plain,(
    k1_relat_1('#skF_9') = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_48,plain,(
    v1_relat_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_46,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_38,plain,(
    k1_relat_1('#skF_8') = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_240,plain,(
    ! [A_82,B_83] :
      ( r2_hidden('#skF_5'(A_82,B_83),k1_relat_1(A_82))
      | B_83 = A_82
      | k1_relat_1(B_83) != k1_relat_1(A_82)
      | ~ v1_funct_1(B_83)
      | ~ v1_relat_1(B_83)
      | ~ v1_funct_1(A_82)
      | ~ v1_relat_1(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_254,plain,(
    ! [B_83] :
      ( r2_hidden('#skF_5'('#skF_8',B_83),'#skF_6')
      | B_83 = '#skF_8'
      | k1_relat_1(B_83) != k1_relat_1('#skF_8')
      | ~ v1_funct_1(B_83)
      | ~ v1_relat_1(B_83)
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_240])).

tff(c_260,plain,(
    ! [B_83] :
      ( r2_hidden('#skF_5'('#skF_8',B_83),'#skF_6')
      | B_83 = '#skF_8'
      | k1_relat_1(B_83) != '#skF_6'
      | ~ v1_funct_1(B_83)
      | ~ v1_relat_1(B_83) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_38,c_254])).

tff(c_52,plain,(
    v1_relat_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_50,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_40,plain,(
    k2_relat_1('#skF_7') = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_76,plain,(
    ! [A_62,C_63] :
      ( k1_funct_1(A_62,'#skF_4'(A_62,k2_relat_1(A_62),C_63)) = C_63
      | ~ r2_hidden(C_63,k2_relat_1(A_62))
      | ~ v1_funct_1(A_62)
      | ~ v1_relat_1(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_92,plain,(
    ! [C_63] :
      ( k1_funct_1('#skF_7','#skF_4'('#skF_7','#skF_6',C_63)) = C_63
      | ~ r2_hidden(C_63,k2_relat_1('#skF_7'))
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_76])).

tff(c_98,plain,(
    ! [C_63] :
      ( k1_funct_1('#skF_7','#skF_4'('#skF_7','#skF_6',C_63)) = C_63
      | ~ r2_hidden(C_63,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_40,c_92])).

tff(c_116,plain,(
    ! [A_65,C_66] :
      ( r2_hidden('#skF_4'(A_65,k2_relat_1(A_65),C_66),k1_relat_1(A_65))
      | ~ r2_hidden(C_66,k2_relat_1(A_65))
      | ~ v1_funct_1(A_65)
      | ~ v1_relat_1(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_125,plain,(
    ! [C_66] :
      ( r2_hidden('#skF_4'('#skF_7','#skF_6',C_66),k1_relat_1('#skF_7'))
      | ~ r2_hidden(C_66,k2_relat_1('#skF_7'))
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_116])).

tff(c_131,plain,(
    ! [C_66] :
      ( r2_hidden('#skF_4'('#skF_7','#skF_6',C_66),k1_relat_1('#skF_7'))
      | ~ r2_hidden(C_66,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_40,c_125])).

tff(c_69,plain,(
    ! [A_59,D_60] :
      ( r2_hidden(k1_funct_1(A_59,D_60),k2_relat_1(A_59))
      | ~ r2_hidden(D_60,k1_relat_1(A_59))
      | ~ v1_funct_1(A_59)
      | ~ v1_relat_1(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_72,plain,(
    ! [D_60] :
      ( r2_hidden(k1_funct_1('#skF_7',D_60),'#skF_6')
      | ~ r2_hidden(D_60,k1_relat_1('#skF_7'))
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_69])).

tff(c_74,plain,(
    ! [D_60] :
      ( r2_hidden(k1_funct_1('#skF_7',D_60),'#skF_6')
      | ~ r2_hidden(D_60,k1_relat_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_72])).

tff(c_34,plain,(
    k5_relat_1('#skF_7','#skF_9') = k5_relat_1('#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_21443,plain,(
    ! [A_631,C_632,B_633] :
      ( r2_hidden(A_631,k1_relat_1(k5_relat_1(C_632,B_633)))
      | ~ r2_hidden(k1_funct_1(C_632,A_631),k1_relat_1(B_633))
      | ~ r2_hidden(A_631,k1_relat_1(C_632))
      | ~ v1_funct_1(C_632)
      | ~ v1_relat_1(C_632)
      | ~ v1_funct_1(B_633)
      | ~ v1_relat_1(B_633) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_21458,plain,(
    ! [A_631,C_632] :
      ( r2_hidden(A_631,k1_relat_1(k5_relat_1(C_632,'#skF_9')))
      | ~ r2_hidden(k1_funct_1(C_632,A_631),'#skF_6')
      | ~ r2_hidden(A_631,k1_relat_1(C_632))
      | ~ v1_funct_1(C_632)
      | ~ v1_relat_1(C_632)
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_21443])).

tff(c_21469,plain,(
    ! [A_634,C_635] :
      ( r2_hidden(A_634,k1_relat_1(k5_relat_1(C_635,'#skF_9')))
      | ~ r2_hidden(k1_funct_1(C_635,A_634),'#skF_6')
      | ~ r2_hidden(A_634,k1_relat_1(C_635))
      | ~ v1_funct_1(C_635)
      | ~ v1_relat_1(C_635) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_21458])).

tff(c_21489,plain,(
    ! [A_634] :
      ( r2_hidden(A_634,k1_relat_1(k5_relat_1('#skF_7','#skF_8')))
      | ~ r2_hidden(k1_funct_1('#skF_7',A_634),'#skF_6')
      | ~ r2_hidden(A_634,k1_relat_1('#skF_7'))
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_21469])).

tff(c_21500,plain,(
    ! [A_634] :
      ( r2_hidden(A_634,k1_relat_1(k5_relat_1('#skF_7','#skF_8')))
      | ~ r2_hidden(k1_funct_1('#skF_7',A_634),'#skF_6')
      | ~ r2_hidden(A_634,k1_relat_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_21489])).

tff(c_21579,plain,(
    ! [C_639,B_640,A_641] :
      ( k1_funct_1(k5_relat_1(C_639,B_640),A_641) = k1_funct_1(B_640,k1_funct_1(C_639,A_641))
      | ~ r2_hidden(A_641,k1_relat_1(k5_relat_1(C_639,B_640)))
      | ~ v1_funct_1(C_639)
      | ~ v1_relat_1(C_639)
      | ~ v1_funct_1(B_640)
      | ~ v1_relat_1(B_640) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_21585,plain,(
    ! [A_634] :
      ( k1_funct_1(k5_relat_1('#skF_7','#skF_8'),A_634) = k1_funct_1('#skF_8',k1_funct_1('#skF_7',A_634))
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7')
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ r2_hidden(k1_funct_1('#skF_7',A_634),'#skF_6')
      | ~ r2_hidden(A_634,k1_relat_1('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_21500,c_21579])).

tff(c_21801,plain,(
    ! [A_647] :
      ( k1_funct_1(k5_relat_1('#skF_7','#skF_8'),A_647) = k1_funct_1('#skF_8',k1_funct_1('#skF_7',A_647))
      | ~ r2_hidden(k1_funct_1('#skF_7',A_647),'#skF_6')
      | ~ r2_hidden(A_647,k1_relat_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_52,c_50,c_21585])).

tff(c_21817,plain,(
    ! [D_648] :
      ( k1_funct_1(k5_relat_1('#skF_7','#skF_8'),D_648) = k1_funct_1('#skF_8',k1_funct_1('#skF_7',D_648))
      | ~ r2_hidden(D_648,k1_relat_1('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_74,c_21801])).

tff(c_21907,plain,(
    ! [C_650] :
      ( k1_funct_1(k5_relat_1('#skF_7','#skF_8'),'#skF_4'('#skF_7','#skF_6',C_650)) = k1_funct_1('#skF_8',k1_funct_1('#skF_7','#skF_4'('#skF_7','#skF_6',C_650)))
      | ~ r2_hidden(C_650,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_131,c_21817])).

tff(c_6,plain,(
    ! [A_1,C_37] :
      ( r2_hidden('#skF_4'(A_1,k2_relat_1(A_1),C_37),k1_relat_1(A_1))
      | ~ r2_hidden(C_37,k2_relat_1(A_1))
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_21461,plain,(
    ! [A_631,C_632] :
      ( r2_hidden(A_631,k1_relat_1(k5_relat_1(C_632,'#skF_8')))
      | ~ r2_hidden(k1_funct_1(C_632,A_631),'#skF_6')
      | ~ r2_hidden(A_631,k1_relat_1(C_632))
      | ~ v1_funct_1(C_632)
      | ~ v1_relat_1(C_632)
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_21443])).

tff(c_21468,plain,(
    ! [A_631,C_632] :
      ( r2_hidden(A_631,k1_relat_1(k5_relat_1(C_632,'#skF_8')))
      | ~ r2_hidden(k1_funct_1(C_632,A_631),'#skF_6')
      | ~ r2_hidden(A_631,k1_relat_1(C_632))
      | ~ v1_funct_1(C_632)
      | ~ v1_relat_1(C_632) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_21461])).

tff(c_21627,plain,(
    ! [A_641] :
      ( k1_funct_1(k5_relat_1('#skF_7','#skF_9'),A_641) = k1_funct_1('#skF_9',k1_funct_1('#skF_7',A_641))
      | ~ r2_hidden(A_641,k1_relat_1(k5_relat_1('#skF_7','#skF_8')))
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7')
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_21579])).

tff(c_21654,plain,(
    ! [A_644] :
      ( k1_funct_1(k5_relat_1('#skF_7','#skF_8'),A_644) = k1_funct_1('#skF_9',k1_funct_1('#skF_7',A_644))
      | ~ r2_hidden(A_644,k1_relat_1(k5_relat_1('#skF_7','#skF_8'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_52,c_50,c_34,c_21627])).

tff(c_21658,plain,(
    ! [A_631] :
      ( k1_funct_1(k5_relat_1('#skF_7','#skF_8'),A_631) = k1_funct_1('#skF_9',k1_funct_1('#skF_7',A_631))
      | ~ r2_hidden(k1_funct_1('#skF_7',A_631),'#skF_6')
      | ~ r2_hidden(A_631,k1_relat_1('#skF_7'))
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_21468,c_21654])).

tff(c_21715,plain,(
    ! [A_645] :
      ( k1_funct_1(k5_relat_1('#skF_7','#skF_8'),A_645) = k1_funct_1('#skF_9',k1_funct_1('#skF_7',A_645))
      | ~ r2_hidden(k1_funct_1('#skF_7',A_645),'#skF_6')
      | ~ r2_hidden(A_645,k1_relat_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_21658])).

tff(c_21731,plain,(
    ! [D_646] :
      ( k1_funct_1(k5_relat_1('#skF_7','#skF_8'),D_646) = k1_funct_1('#skF_9',k1_funct_1('#skF_7',D_646))
      | ~ r2_hidden(D_646,k1_relat_1('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_74,c_21715])).

tff(c_21779,plain,(
    ! [C_37] :
      ( k1_funct_1(k5_relat_1('#skF_7','#skF_8'),'#skF_4'('#skF_7',k2_relat_1('#skF_7'),C_37)) = k1_funct_1('#skF_9',k1_funct_1('#skF_7','#skF_4'('#skF_7',k2_relat_1('#skF_7'),C_37)))
      | ~ r2_hidden(C_37,k2_relat_1('#skF_7'))
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_6,c_21731])).

tff(c_21800,plain,(
    ! [C_37] :
      ( k1_funct_1(k5_relat_1('#skF_7','#skF_8'),'#skF_4'('#skF_7','#skF_6',C_37)) = k1_funct_1('#skF_9',k1_funct_1('#skF_7','#skF_4'('#skF_7','#skF_6',C_37)))
      | ~ r2_hidden(C_37,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_40,c_40,c_40,c_21779])).

tff(c_26276,plain,(
    ! [C_797] :
      ( k1_funct_1('#skF_9',k1_funct_1('#skF_7','#skF_4'('#skF_7','#skF_6',C_797))) = k1_funct_1('#skF_8',k1_funct_1('#skF_7','#skF_4'('#skF_7','#skF_6',C_797)))
      | ~ r2_hidden(C_797,'#skF_6')
      | ~ r2_hidden(C_797,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_21907,c_21800])).

tff(c_26311,plain,(
    ! [C_798] :
      ( k1_funct_1('#skF_8',k1_funct_1('#skF_7','#skF_4'('#skF_7','#skF_6',C_798))) = k1_funct_1('#skF_9',C_798)
      | ~ r2_hidden(C_798,'#skF_6')
      | ~ r2_hidden(C_798,'#skF_6')
      | ~ r2_hidden(C_798,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_98,c_26276])).

tff(c_27183,plain,(
    ! [C_832] :
      ( k1_funct_1('#skF_9',C_832) = k1_funct_1('#skF_8',C_832)
      | ~ r2_hidden(C_832,'#skF_6')
      | ~ r2_hidden(C_832,'#skF_6')
      | ~ r2_hidden(C_832,'#skF_6')
      | ~ r2_hidden(C_832,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_98,c_26311])).

tff(c_36575,plain,(
    ! [B_1046] :
      ( k1_funct_1('#skF_9','#skF_5'('#skF_8',B_1046)) = k1_funct_1('#skF_8','#skF_5'('#skF_8',B_1046))
      | ~ r2_hidden('#skF_5'('#skF_8',B_1046),'#skF_6')
      | B_1046 = '#skF_8'
      | k1_relat_1(B_1046) != '#skF_6'
      | ~ v1_funct_1(B_1046)
      | ~ v1_relat_1(B_1046) ) ),
    inference(resolution,[status(thm)],[c_260,c_27183])).

tff(c_36580,plain,(
    ! [B_1047] :
      ( k1_funct_1('#skF_9','#skF_5'('#skF_8',B_1047)) = k1_funct_1('#skF_8','#skF_5'('#skF_8',B_1047))
      | B_1047 = '#skF_8'
      | k1_relat_1(B_1047) != '#skF_6'
      | ~ v1_funct_1(B_1047)
      | ~ v1_relat_1(B_1047) ) ),
    inference(resolution,[status(thm)],[c_260,c_36575])).

tff(c_28,plain,(
    ! [B_53,A_49] :
      ( k1_funct_1(B_53,'#skF_5'(A_49,B_53)) != k1_funct_1(A_49,'#skF_5'(A_49,B_53))
      | B_53 = A_49
      | k1_relat_1(B_53) != k1_relat_1(A_49)
      | ~ v1_funct_1(B_53)
      | ~ v1_relat_1(B_53)
      | ~ v1_funct_1(A_49)
      | ~ v1_relat_1(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_36618,plain,
    ( k1_relat_1('#skF_9') != k1_relat_1('#skF_8')
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8')
    | '#skF_9' = '#skF_8'
    | k1_relat_1('#skF_9') != '#skF_6'
    | ~ v1_funct_1('#skF_9')
    | ~ v1_relat_1('#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_36580,c_28])).

tff(c_36642,plain,(
    '#skF_9' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_36,c_48,c_46,c_38,c_36,c_36618])).

tff(c_36644,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_36642])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:31:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 14.85/7.12  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.85/7.13  
% 14.85/7.13  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.85/7.13  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k5_relat_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_4 > #skF_7 > #skF_3 > #skF_6 > #skF_9 > #skF_8 > #skF_2 > #skF_1 > #skF_5
% 14.85/7.13  
% 14.85/7.13  %Foreground sorts:
% 14.85/7.13  
% 14.85/7.13  
% 14.85/7.13  %Background operators:
% 14.85/7.13  
% 14.85/7.13  
% 14.85/7.13  %Foreground operators:
% 14.85/7.13  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 14.85/7.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 14.85/7.13  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 14.85/7.13  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 14.85/7.13  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 14.85/7.13  tff('#skF_7', type, '#skF_7': $i).
% 14.85/7.13  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 14.85/7.13  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 14.85/7.13  tff('#skF_6', type, '#skF_6': $i).
% 14.85/7.13  tff('#skF_9', type, '#skF_9': $i).
% 14.85/7.13  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 14.85/7.13  tff('#skF_8', type, '#skF_8': $i).
% 14.85/7.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 14.85/7.13  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 14.85/7.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 14.85/7.13  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 14.85/7.13  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 14.85/7.13  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 14.85/7.13  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 14.85/7.13  
% 14.98/7.15  tff(f_111, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (![D]: ((v1_relat_1(D) & v1_funct_1(D)) => (((((A = k2_relat_1(B)) & (k1_relat_1(C) = A)) & (k1_relat_1(D) = A)) & (k5_relat_1(B, C) = k5_relat_1(B, D))) => (C = D)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t156_funct_1)).
% 14.98/7.15  tff(f_86, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((k1_relat_1(A) = k1_relat_1(B)) & (![C]: (r2_hidden(C, k1_relat_1(A)) => (k1_funct_1(A, C) = k1_funct_1(B, C))))) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_funct_1)).
% 14.98/7.15  tff(f_40, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_funct_1)).
% 14.98/7.15  tff(f_55, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(k5_relat_1(C, B))) <=> (r2_hidden(A, k1_relat_1(C)) & r2_hidden(k1_funct_1(C, A), k1_relat_1(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_funct_1)).
% 14.98/7.15  tff(f_68, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(k5_relat_1(C, B))) => (k1_funct_1(k5_relat_1(C, B), A) = k1_funct_1(B, k1_funct_1(C, A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_funct_1)).
% 14.98/7.15  tff(c_32, plain, ('#skF_9'!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_111])).
% 14.98/7.15  tff(c_44, plain, (v1_relat_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_111])).
% 14.98/7.15  tff(c_42, plain, (v1_funct_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_111])).
% 14.98/7.15  tff(c_36, plain, (k1_relat_1('#skF_9')='#skF_6'), inference(cnfTransformation, [status(thm)], [f_111])).
% 14.98/7.15  tff(c_48, plain, (v1_relat_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_111])).
% 14.98/7.15  tff(c_46, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_111])).
% 14.98/7.15  tff(c_38, plain, (k1_relat_1('#skF_8')='#skF_6'), inference(cnfTransformation, [status(thm)], [f_111])).
% 14.98/7.15  tff(c_240, plain, (![A_82, B_83]: (r2_hidden('#skF_5'(A_82, B_83), k1_relat_1(A_82)) | B_83=A_82 | k1_relat_1(B_83)!=k1_relat_1(A_82) | ~v1_funct_1(B_83) | ~v1_relat_1(B_83) | ~v1_funct_1(A_82) | ~v1_relat_1(A_82))), inference(cnfTransformation, [status(thm)], [f_86])).
% 14.98/7.15  tff(c_254, plain, (![B_83]: (r2_hidden('#skF_5'('#skF_8', B_83), '#skF_6') | B_83='#skF_8' | k1_relat_1(B_83)!=k1_relat_1('#skF_8') | ~v1_funct_1(B_83) | ~v1_relat_1(B_83) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_38, c_240])).
% 14.98/7.15  tff(c_260, plain, (![B_83]: (r2_hidden('#skF_5'('#skF_8', B_83), '#skF_6') | B_83='#skF_8' | k1_relat_1(B_83)!='#skF_6' | ~v1_funct_1(B_83) | ~v1_relat_1(B_83))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_38, c_254])).
% 14.98/7.15  tff(c_52, plain, (v1_relat_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_111])).
% 14.98/7.15  tff(c_50, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_111])).
% 14.98/7.15  tff(c_40, plain, (k2_relat_1('#skF_7')='#skF_6'), inference(cnfTransformation, [status(thm)], [f_111])).
% 14.98/7.15  tff(c_76, plain, (![A_62, C_63]: (k1_funct_1(A_62, '#skF_4'(A_62, k2_relat_1(A_62), C_63))=C_63 | ~r2_hidden(C_63, k2_relat_1(A_62)) | ~v1_funct_1(A_62) | ~v1_relat_1(A_62))), inference(cnfTransformation, [status(thm)], [f_40])).
% 14.98/7.15  tff(c_92, plain, (![C_63]: (k1_funct_1('#skF_7', '#skF_4'('#skF_7', '#skF_6', C_63))=C_63 | ~r2_hidden(C_63, k2_relat_1('#skF_7')) | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_40, c_76])).
% 14.98/7.15  tff(c_98, plain, (![C_63]: (k1_funct_1('#skF_7', '#skF_4'('#skF_7', '#skF_6', C_63))=C_63 | ~r2_hidden(C_63, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_40, c_92])).
% 14.98/7.15  tff(c_116, plain, (![A_65, C_66]: (r2_hidden('#skF_4'(A_65, k2_relat_1(A_65), C_66), k1_relat_1(A_65)) | ~r2_hidden(C_66, k2_relat_1(A_65)) | ~v1_funct_1(A_65) | ~v1_relat_1(A_65))), inference(cnfTransformation, [status(thm)], [f_40])).
% 14.98/7.15  tff(c_125, plain, (![C_66]: (r2_hidden('#skF_4'('#skF_7', '#skF_6', C_66), k1_relat_1('#skF_7')) | ~r2_hidden(C_66, k2_relat_1('#skF_7')) | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_40, c_116])).
% 14.98/7.15  tff(c_131, plain, (![C_66]: (r2_hidden('#skF_4'('#skF_7', '#skF_6', C_66), k1_relat_1('#skF_7')) | ~r2_hidden(C_66, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_40, c_125])).
% 14.98/7.15  tff(c_69, plain, (![A_59, D_60]: (r2_hidden(k1_funct_1(A_59, D_60), k2_relat_1(A_59)) | ~r2_hidden(D_60, k1_relat_1(A_59)) | ~v1_funct_1(A_59) | ~v1_relat_1(A_59))), inference(cnfTransformation, [status(thm)], [f_40])).
% 14.98/7.15  tff(c_72, plain, (![D_60]: (r2_hidden(k1_funct_1('#skF_7', D_60), '#skF_6') | ~r2_hidden(D_60, k1_relat_1('#skF_7')) | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_40, c_69])).
% 14.98/7.15  tff(c_74, plain, (![D_60]: (r2_hidden(k1_funct_1('#skF_7', D_60), '#skF_6') | ~r2_hidden(D_60, k1_relat_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_72])).
% 14.98/7.15  tff(c_34, plain, (k5_relat_1('#skF_7', '#skF_9')=k5_relat_1('#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_111])).
% 14.98/7.15  tff(c_21443, plain, (![A_631, C_632, B_633]: (r2_hidden(A_631, k1_relat_1(k5_relat_1(C_632, B_633))) | ~r2_hidden(k1_funct_1(C_632, A_631), k1_relat_1(B_633)) | ~r2_hidden(A_631, k1_relat_1(C_632)) | ~v1_funct_1(C_632) | ~v1_relat_1(C_632) | ~v1_funct_1(B_633) | ~v1_relat_1(B_633))), inference(cnfTransformation, [status(thm)], [f_55])).
% 14.98/7.15  tff(c_21458, plain, (![A_631, C_632]: (r2_hidden(A_631, k1_relat_1(k5_relat_1(C_632, '#skF_9'))) | ~r2_hidden(k1_funct_1(C_632, A_631), '#skF_6') | ~r2_hidden(A_631, k1_relat_1(C_632)) | ~v1_funct_1(C_632) | ~v1_relat_1(C_632) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_36, c_21443])).
% 14.98/7.15  tff(c_21469, plain, (![A_634, C_635]: (r2_hidden(A_634, k1_relat_1(k5_relat_1(C_635, '#skF_9'))) | ~r2_hidden(k1_funct_1(C_635, A_634), '#skF_6') | ~r2_hidden(A_634, k1_relat_1(C_635)) | ~v1_funct_1(C_635) | ~v1_relat_1(C_635))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_21458])).
% 14.98/7.15  tff(c_21489, plain, (![A_634]: (r2_hidden(A_634, k1_relat_1(k5_relat_1('#skF_7', '#skF_8'))) | ~r2_hidden(k1_funct_1('#skF_7', A_634), '#skF_6') | ~r2_hidden(A_634, k1_relat_1('#skF_7')) | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_34, c_21469])).
% 14.98/7.15  tff(c_21500, plain, (![A_634]: (r2_hidden(A_634, k1_relat_1(k5_relat_1('#skF_7', '#skF_8'))) | ~r2_hidden(k1_funct_1('#skF_7', A_634), '#skF_6') | ~r2_hidden(A_634, k1_relat_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_21489])).
% 14.98/7.15  tff(c_21579, plain, (![C_639, B_640, A_641]: (k1_funct_1(k5_relat_1(C_639, B_640), A_641)=k1_funct_1(B_640, k1_funct_1(C_639, A_641)) | ~r2_hidden(A_641, k1_relat_1(k5_relat_1(C_639, B_640))) | ~v1_funct_1(C_639) | ~v1_relat_1(C_639) | ~v1_funct_1(B_640) | ~v1_relat_1(B_640))), inference(cnfTransformation, [status(thm)], [f_68])).
% 14.98/7.15  tff(c_21585, plain, (![A_634]: (k1_funct_1(k5_relat_1('#skF_7', '#skF_8'), A_634)=k1_funct_1('#skF_8', k1_funct_1('#skF_7', A_634)) | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7') | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r2_hidden(k1_funct_1('#skF_7', A_634), '#skF_6') | ~r2_hidden(A_634, k1_relat_1('#skF_7')))), inference(resolution, [status(thm)], [c_21500, c_21579])).
% 14.98/7.15  tff(c_21801, plain, (![A_647]: (k1_funct_1(k5_relat_1('#skF_7', '#skF_8'), A_647)=k1_funct_1('#skF_8', k1_funct_1('#skF_7', A_647)) | ~r2_hidden(k1_funct_1('#skF_7', A_647), '#skF_6') | ~r2_hidden(A_647, k1_relat_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_52, c_50, c_21585])).
% 14.98/7.15  tff(c_21817, plain, (![D_648]: (k1_funct_1(k5_relat_1('#skF_7', '#skF_8'), D_648)=k1_funct_1('#skF_8', k1_funct_1('#skF_7', D_648)) | ~r2_hidden(D_648, k1_relat_1('#skF_7')))), inference(resolution, [status(thm)], [c_74, c_21801])).
% 14.98/7.15  tff(c_21907, plain, (![C_650]: (k1_funct_1(k5_relat_1('#skF_7', '#skF_8'), '#skF_4'('#skF_7', '#skF_6', C_650))=k1_funct_1('#skF_8', k1_funct_1('#skF_7', '#skF_4'('#skF_7', '#skF_6', C_650))) | ~r2_hidden(C_650, '#skF_6'))), inference(resolution, [status(thm)], [c_131, c_21817])).
% 14.98/7.15  tff(c_6, plain, (![A_1, C_37]: (r2_hidden('#skF_4'(A_1, k2_relat_1(A_1), C_37), k1_relat_1(A_1)) | ~r2_hidden(C_37, k2_relat_1(A_1)) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_40])).
% 14.98/7.15  tff(c_21461, plain, (![A_631, C_632]: (r2_hidden(A_631, k1_relat_1(k5_relat_1(C_632, '#skF_8'))) | ~r2_hidden(k1_funct_1(C_632, A_631), '#skF_6') | ~r2_hidden(A_631, k1_relat_1(C_632)) | ~v1_funct_1(C_632) | ~v1_relat_1(C_632) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_38, c_21443])).
% 14.98/7.15  tff(c_21468, plain, (![A_631, C_632]: (r2_hidden(A_631, k1_relat_1(k5_relat_1(C_632, '#skF_8'))) | ~r2_hidden(k1_funct_1(C_632, A_631), '#skF_6') | ~r2_hidden(A_631, k1_relat_1(C_632)) | ~v1_funct_1(C_632) | ~v1_relat_1(C_632))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_21461])).
% 14.98/7.15  tff(c_21627, plain, (![A_641]: (k1_funct_1(k5_relat_1('#skF_7', '#skF_9'), A_641)=k1_funct_1('#skF_9', k1_funct_1('#skF_7', A_641)) | ~r2_hidden(A_641, k1_relat_1(k5_relat_1('#skF_7', '#skF_8'))) | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7') | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_34, c_21579])).
% 14.98/7.15  tff(c_21654, plain, (![A_644]: (k1_funct_1(k5_relat_1('#skF_7', '#skF_8'), A_644)=k1_funct_1('#skF_9', k1_funct_1('#skF_7', A_644)) | ~r2_hidden(A_644, k1_relat_1(k5_relat_1('#skF_7', '#skF_8'))))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_52, c_50, c_34, c_21627])).
% 14.98/7.15  tff(c_21658, plain, (![A_631]: (k1_funct_1(k5_relat_1('#skF_7', '#skF_8'), A_631)=k1_funct_1('#skF_9', k1_funct_1('#skF_7', A_631)) | ~r2_hidden(k1_funct_1('#skF_7', A_631), '#skF_6') | ~r2_hidden(A_631, k1_relat_1('#skF_7')) | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_21468, c_21654])).
% 14.98/7.15  tff(c_21715, plain, (![A_645]: (k1_funct_1(k5_relat_1('#skF_7', '#skF_8'), A_645)=k1_funct_1('#skF_9', k1_funct_1('#skF_7', A_645)) | ~r2_hidden(k1_funct_1('#skF_7', A_645), '#skF_6') | ~r2_hidden(A_645, k1_relat_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_21658])).
% 14.98/7.15  tff(c_21731, plain, (![D_646]: (k1_funct_1(k5_relat_1('#skF_7', '#skF_8'), D_646)=k1_funct_1('#skF_9', k1_funct_1('#skF_7', D_646)) | ~r2_hidden(D_646, k1_relat_1('#skF_7')))), inference(resolution, [status(thm)], [c_74, c_21715])).
% 14.98/7.15  tff(c_21779, plain, (![C_37]: (k1_funct_1(k5_relat_1('#skF_7', '#skF_8'), '#skF_4'('#skF_7', k2_relat_1('#skF_7'), C_37))=k1_funct_1('#skF_9', k1_funct_1('#skF_7', '#skF_4'('#skF_7', k2_relat_1('#skF_7'), C_37))) | ~r2_hidden(C_37, k2_relat_1('#skF_7')) | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_6, c_21731])).
% 14.98/7.15  tff(c_21800, plain, (![C_37]: (k1_funct_1(k5_relat_1('#skF_7', '#skF_8'), '#skF_4'('#skF_7', '#skF_6', C_37))=k1_funct_1('#skF_9', k1_funct_1('#skF_7', '#skF_4'('#skF_7', '#skF_6', C_37))) | ~r2_hidden(C_37, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_40, c_40, c_40, c_21779])).
% 14.98/7.15  tff(c_26276, plain, (![C_797]: (k1_funct_1('#skF_9', k1_funct_1('#skF_7', '#skF_4'('#skF_7', '#skF_6', C_797)))=k1_funct_1('#skF_8', k1_funct_1('#skF_7', '#skF_4'('#skF_7', '#skF_6', C_797))) | ~r2_hidden(C_797, '#skF_6') | ~r2_hidden(C_797, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_21907, c_21800])).
% 14.98/7.15  tff(c_26311, plain, (![C_798]: (k1_funct_1('#skF_8', k1_funct_1('#skF_7', '#skF_4'('#skF_7', '#skF_6', C_798)))=k1_funct_1('#skF_9', C_798) | ~r2_hidden(C_798, '#skF_6') | ~r2_hidden(C_798, '#skF_6') | ~r2_hidden(C_798, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_98, c_26276])).
% 14.98/7.15  tff(c_27183, plain, (![C_832]: (k1_funct_1('#skF_9', C_832)=k1_funct_1('#skF_8', C_832) | ~r2_hidden(C_832, '#skF_6') | ~r2_hidden(C_832, '#skF_6') | ~r2_hidden(C_832, '#skF_6') | ~r2_hidden(C_832, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_98, c_26311])).
% 14.98/7.15  tff(c_36575, plain, (![B_1046]: (k1_funct_1('#skF_9', '#skF_5'('#skF_8', B_1046))=k1_funct_1('#skF_8', '#skF_5'('#skF_8', B_1046)) | ~r2_hidden('#skF_5'('#skF_8', B_1046), '#skF_6') | B_1046='#skF_8' | k1_relat_1(B_1046)!='#skF_6' | ~v1_funct_1(B_1046) | ~v1_relat_1(B_1046))), inference(resolution, [status(thm)], [c_260, c_27183])).
% 14.98/7.15  tff(c_36580, plain, (![B_1047]: (k1_funct_1('#skF_9', '#skF_5'('#skF_8', B_1047))=k1_funct_1('#skF_8', '#skF_5'('#skF_8', B_1047)) | B_1047='#skF_8' | k1_relat_1(B_1047)!='#skF_6' | ~v1_funct_1(B_1047) | ~v1_relat_1(B_1047))), inference(resolution, [status(thm)], [c_260, c_36575])).
% 14.98/7.15  tff(c_28, plain, (![B_53, A_49]: (k1_funct_1(B_53, '#skF_5'(A_49, B_53))!=k1_funct_1(A_49, '#skF_5'(A_49, B_53)) | B_53=A_49 | k1_relat_1(B_53)!=k1_relat_1(A_49) | ~v1_funct_1(B_53) | ~v1_relat_1(B_53) | ~v1_funct_1(A_49) | ~v1_relat_1(A_49))), inference(cnfTransformation, [status(thm)], [f_86])).
% 14.98/7.15  tff(c_36618, plain, (k1_relat_1('#skF_9')!=k1_relat_1('#skF_8') | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | '#skF_9'='#skF_8' | k1_relat_1('#skF_9')!='#skF_6' | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_36580, c_28])).
% 14.98/7.15  tff(c_36642, plain, ('#skF_9'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_36, c_48, c_46, c_38, c_36, c_36618])).
% 14.98/7.15  tff(c_36644, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_36642])).
% 14.98/7.15  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.98/7.15  
% 14.98/7.15  Inference rules
% 14.98/7.15  ----------------------
% 14.98/7.15  #Ref     : 27
% 14.98/7.15  #Sup     : 7533
% 14.98/7.15  #Fact    : 0
% 14.98/7.15  #Define  : 0
% 14.98/7.15  #Split   : 52
% 14.98/7.15  #Chain   : 0
% 14.98/7.15  #Close   : 0
% 14.98/7.15  
% 14.98/7.15  Ordering : KBO
% 14.98/7.15  
% 14.98/7.15  Simplification rules
% 14.98/7.15  ----------------------
% 14.98/7.15  #Subsume      : 1269
% 14.98/7.15  #Demod        : 9824
% 14.98/7.15  #Tautology    : 1591
% 14.98/7.15  #SimpNegUnit  : 239
% 14.98/7.15  #BackRed      : 173
% 14.98/7.15  
% 14.98/7.15  #Partial instantiations: 0
% 14.98/7.15  #Strategies tried      : 1
% 14.98/7.15  
% 14.98/7.15  Timing (in seconds)
% 14.98/7.15  ----------------------
% 14.98/7.15  Preprocessing        : 0.32
% 14.98/7.15  Parsing              : 0.16
% 14.98/7.15  CNF conversion       : 0.03
% 14.98/7.15  Main loop            : 6.06
% 14.98/7.15  Inferencing          : 1.76
% 14.98/7.15  Reduction            : 2.18
% 14.98/7.15  Demodulation         : 1.65
% 14.98/7.15  BG Simplification    : 0.20
% 14.98/7.15  Subsumption          : 1.51
% 14.98/7.15  Abstraction          : 0.34
% 14.98/7.15  MUC search           : 0.00
% 14.98/7.15  Cooper               : 0.00
% 14.98/7.15  Total                : 6.41
% 14.98/7.15  Index Insertion      : 0.00
% 14.98/7.15  Index Deletion       : 0.00
% 14.98/7.15  Index Matching       : 0.00
% 14.98/7.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
