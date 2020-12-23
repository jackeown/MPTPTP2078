%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:31 EST 2020

% Result     : Theorem 3.23s
% Output     : CNFRefutation 3.57s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 213 expanded)
%              Number of leaves         :   42 (  95 expanded)
%              Depth                    :   17
%              Number of atoms          :  150 ( 557 expanded)
%              Number of equality atoms :   36 ( 125 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > r1_xboole_0 > m1_subset_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k7_subset_1 > k3_yellow19 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_yellow19 > #nlpp > u1_struct_0 > k3_yellow_1 > k3_lattice3 > k2_struct_0 > k1_zfmisc_1 > k1_tarski > k1_lattice3 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k3_lattice3,type,(
    k3_lattice3: $i > $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_yellow_1,type,(
    k3_yellow_1: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v2_waybel_0,type,(
    v2_waybel_0: ( $i * $i ) > $o )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_lattice3,type,(
    k1_lattice3: $i > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(k2_yellow19,type,(
    k2_yellow19: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_yellow19,type,(
    k3_yellow19: ( $i * $i * $i ) > $i )).

tff(v13_waybel_0,type,(
    v13_waybel_0: ( $i * $i ) > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_136,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & l1_struct_0(A) )
       => ! [B] :
            ( ( ~ v1_xboole_0(B)
              & v1_subset_1(B,u1_struct_0(k3_yellow_1(k2_struct_0(A))))
              & v2_waybel_0(B,k3_yellow_1(k2_struct_0(A)))
              & v13_waybel_0(B,k3_yellow_1(k2_struct_0(A)))
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A))))) )
           => B = k2_yellow19(A,k3_yellow19(A,k2_struct_0(A),B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_yellow19)).

tff(f_30,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_95,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v2_waybel_0(B,k3_yellow_1(k2_struct_0(A)))
            & v13_waybel_0(B,k3_yellow_1(k2_struct_0(A)))
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A))))) )
         => k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A))),B,k1_tarski(k1_xboole_0)) = k2_yellow19(A,k3_yellow19(A,k2_struct_0(A),B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_yellow19)).

tff(f_52,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_54,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_50,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_64,axiom,(
    ! [A,B] :
      ( A != B
     => r1_xboole_0(k1_tarski(A),k1_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_zfmisc_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(f_116,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_subset_1(B,u1_struct_0(k3_yellow_1(A)))
            & v2_waybel_0(B,k3_yellow_1(A))
            & v13_waybel_0(B,k3_yellow_1(A))
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(k3_yellow_1(A)))) )
         => ! [C] :
              ~ ( r2_hidden(C,B)
                & v1_xboole_0(C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_yellow19)).

tff(f_76,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(k2_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_struct_0)).

tff(c_48,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_46,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_42,plain,(
    v1_subset_1('#skF_3',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_40,plain,(
    v2_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_38,plain,(
    v13_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_36,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2'))))) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_44,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_222,plain,(
    ! [A_63,B_64,C_65] :
      ( k7_subset_1(A_63,B_64,C_65) = k4_xboole_0(B_64,C_65)
      | ~ m1_subset_1(B_64,k1_zfmisc_1(A_63)) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_225,plain,(
    ! [C_65] : k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2'))),'#skF_3',C_65) = k4_xboole_0('#skF_3',C_65) ),
    inference(resolution,[status(thm)],[c_36,c_222])).

tff(c_318,plain,(
    ! [A_86,B_87] :
      ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_86))),B_87,k1_tarski(k1_xboole_0)) = k2_yellow19(A_86,k3_yellow19(A_86,k2_struct_0(A_86),B_87))
      | ~ m1_subset_1(B_87,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_86)))))
      | ~ v13_waybel_0(B_87,k3_yellow_1(k2_struct_0(A_86)))
      | ~ v2_waybel_0(B_87,k3_yellow_1(k2_struct_0(A_86)))
      | v1_xboole_0(B_87)
      | ~ l1_struct_0(A_86)
      | v2_struct_0(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_320,plain,
    ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2'))),'#skF_3',k1_tarski(k1_xboole_0)) = k2_yellow19('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))
    | ~ v13_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
    | ~ v2_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
    | v1_xboole_0('#skF_3')
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_318])).

tff(c_323,plain,
    ( k2_yellow19('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3')) = k4_xboole_0('#skF_3',k1_tarski(k1_xboole_0))
    | v1_xboole_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_40,c_38,c_225,c_320])).

tff(c_324,plain,(
    k2_yellow19('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3')) = k4_xboole_0('#skF_3',k1_tarski(k1_xboole_0)) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_44,c_323])).

tff(c_34,plain,(
    k2_yellow19('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3')) != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_459,plain,(
    k4_xboole_0('#skF_3',k1_tarski(k1_xboole_0)) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_324,c_34])).

tff(c_16,plain,(
    ! [A_10] : k4_xboole_0(A_10,k1_xboole_0) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_18,plain,(
    ! [A_11] : r1_xboole_0(A_11,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_70,plain,(
    ! [A_39,B_40] :
      ( k3_xboole_0(A_39,B_40) = k1_xboole_0
      | ~ r1_xboole_0(A_39,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_82,plain,(
    ! [A_11] : k3_xboole_0(A_11,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_18,c_70])).

tff(c_151,plain,(
    ! [A_54,B_55] : k5_xboole_0(A_54,k3_xboole_0(A_54,B_55)) = k4_xboole_0(A_54,B_55) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_163,plain,(
    ! [A_11] : k5_xboole_0(A_11,k1_xboole_0) = k4_xboole_0(A_11,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_151])).

tff(c_166,plain,(
    ! [A_11] : k5_xboole_0(A_11,k1_xboole_0) = A_11 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_163])).

tff(c_108,plain,(
    ! [A_48,B_49] :
      ( r2_hidden('#skF_1'(A_48,B_49),B_49)
      | r1_xboole_0(A_48,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_22,plain,(
    ! [A_14,B_15] :
      ( r1_xboole_0(k1_tarski(A_14),k1_tarski(B_15))
      | B_15 = A_14 ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_91,plain,(
    ! [A_43,B_44] :
      ( ~ r2_hidden(A_43,B_44)
      | ~ r1_xboole_0(k1_tarski(A_43),B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_103,plain,(
    ! [A_14,B_15] :
      ( ~ r2_hidden(A_14,k1_tarski(B_15))
      | B_15 = A_14 ) ),
    inference(resolution,[status(thm)],[c_22,c_91])).

tff(c_236,plain,(
    ! [A_68,B_69] :
      ( '#skF_1'(A_68,k1_tarski(B_69)) = B_69
      | r1_xboole_0(A_68,k1_tarski(B_69)) ) ),
    inference(resolution,[status(thm)],[c_108,c_103])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_346,plain,(
    ! [A_90,B_91] :
      ( k3_xboole_0(A_90,k1_tarski(B_91)) = k1_xboole_0
      | '#skF_1'(A_90,k1_tarski(B_91)) = B_91 ) ),
    inference(resolution,[status(thm)],[c_236,c_2])).

tff(c_14,plain,(
    ! [A_8,B_9] : k5_xboole_0(A_8,k3_xboole_0(A_8,B_9)) = k4_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_360,plain,(
    ! [A_90,B_91] :
      ( k4_xboole_0(A_90,k1_tarski(B_91)) = k5_xboole_0(A_90,k1_xboole_0)
      | '#skF_1'(A_90,k1_tarski(B_91)) = B_91 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_346,c_14])).

tff(c_378,plain,(
    ! [A_90,B_91] :
      ( k4_xboole_0(A_90,k1_tarski(B_91)) = A_90
      | '#skF_1'(A_90,k1_tarski(B_91)) = B_91 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_166,c_360])).

tff(c_467,plain,(
    '#skF_1'('#skF_3',k1_tarski(k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_378,c_459])).

tff(c_12,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_471,plain,
    ( r2_hidden(k1_xboole_0,'#skF_3')
    | r1_xboole_0('#skF_3',k1_tarski(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_467,c_12])).

tff(c_478,plain,(
    r1_xboole_0('#skF_3',k1_tarski(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_471])).

tff(c_485,plain,(
    k3_xboole_0('#skF_3',k1_tarski(k1_xboole_0)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_478,c_2])).

tff(c_493,plain,(
    k4_xboole_0('#skF_3',k1_tarski(k1_xboole_0)) = k5_xboole_0('#skF_3',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_485,c_14])).

tff(c_501,plain,(
    k4_xboole_0('#skF_3',k1_tarski(k1_xboole_0)) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_166,c_493])).

tff(c_503,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_459,c_501])).

tff(c_504,plain,(
    r2_hidden(k1_xboole_0,'#skF_3') ),
    inference(splitRight,[status(thm)],[c_471])).

tff(c_32,plain,(
    ! [C_30,B_28,A_24] :
      ( ~ v1_xboole_0(C_30)
      | ~ r2_hidden(C_30,B_28)
      | ~ m1_subset_1(B_28,k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_24))))
      | ~ v13_waybel_0(B_28,k3_yellow_1(A_24))
      | ~ v2_waybel_0(B_28,k3_yellow_1(A_24))
      | ~ v1_subset_1(B_28,u1_struct_0(k3_yellow_1(A_24)))
      | v1_xboole_0(B_28)
      | v1_xboole_0(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_509,plain,(
    ! [A_24] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_24))))
      | ~ v13_waybel_0('#skF_3',k3_yellow_1(A_24))
      | ~ v2_waybel_0('#skF_3',k3_yellow_1(A_24))
      | ~ v1_subset_1('#skF_3',u1_struct_0(k3_yellow_1(A_24)))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_24) ) ),
    inference(resolution,[status(thm)],[c_504,c_32])).

tff(c_513,plain,(
    ! [A_24] :
      ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_24))))
      | ~ v13_waybel_0('#skF_3',k3_yellow_1(A_24))
      | ~ v2_waybel_0('#skF_3',k3_yellow_1(A_24))
      | ~ v1_subset_1('#skF_3',u1_struct_0(k3_yellow_1(A_24)))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_24) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_509])).

tff(c_569,plain,(
    ! [A_100] :
      ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_100))))
      | ~ v13_waybel_0('#skF_3',k3_yellow_1(A_100))
      | ~ v2_waybel_0('#skF_3',k3_yellow_1(A_100))
      | ~ v1_subset_1('#skF_3',u1_struct_0(k3_yellow_1(A_100)))
      | v1_xboole_0(A_100) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_513])).

tff(c_572,plain,
    ( ~ v13_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
    | ~ v2_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
    | ~ v1_subset_1('#skF_3',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2'))))
    | v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_36,c_569])).

tff(c_575,plain,(
    v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_572])).

tff(c_26,plain,(
    ! [A_19] :
      ( ~ v1_xboole_0(k2_struct_0(A_19))
      | ~ l1_struct_0(A_19)
      | v2_struct_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_578,plain,
    ( ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_575,c_26])).

tff(c_581,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_578])).

tff(c_583,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_581])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:25:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.23/1.92  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.23/1.93  
% 3.23/1.93  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.23/1.93  %$ v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > r1_xboole_0 > m1_subset_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k7_subset_1 > k3_yellow19 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_yellow19 > #nlpp > u1_struct_0 > k3_yellow_1 > k3_lattice3 > k2_struct_0 > k1_zfmisc_1 > k1_tarski > k1_lattice3 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.23/1.93  
% 3.23/1.93  %Foreground sorts:
% 3.23/1.93  
% 3.23/1.93  
% 3.23/1.93  %Background operators:
% 3.23/1.93  
% 3.23/1.93  
% 3.23/1.93  %Foreground operators:
% 3.23/1.93  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.23/1.93  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.23/1.93  tff(k3_lattice3, type, k3_lattice3: $i > $i).
% 3.23/1.93  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.23/1.93  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 3.23/1.93  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.23/1.93  tff(k3_yellow_1, type, k3_yellow_1: $i > $i).
% 3.23/1.93  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.23/1.93  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.23/1.93  tff(v2_waybel_0, type, v2_waybel_0: ($i * $i) > $o).
% 3.23/1.93  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.23/1.93  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.23/1.93  tff('#skF_2', type, '#skF_2': $i).
% 3.23/1.93  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 3.23/1.93  tff('#skF_3', type, '#skF_3': $i).
% 3.23/1.93  tff(k1_lattice3, type, k1_lattice3: $i > $i).
% 3.23/1.93  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.23/1.93  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.23/1.93  tff(k2_yellow19, type, k2_yellow19: ($i * $i) > $i).
% 3.23/1.93  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.23/1.93  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.23/1.93  tff(k3_yellow19, type, k3_yellow19: ($i * $i * $i) > $i).
% 3.23/1.93  tff(v13_waybel_0, type, v13_waybel_0: ($i * $i) > $o).
% 3.23/1.93  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.23/1.93  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.23/1.93  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.23/1.93  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.23/1.93  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.23/1.93  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.23/1.93  
% 3.57/1.96  tff(f_136, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: (((((~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(k3_yellow_1(k2_struct_0(A))))) & v2_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (B = k2_yellow19(A, k3_yellow19(A, k2_struct_0(A), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_yellow19)).
% 3.57/1.96  tff(f_30, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.57/1.96  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 3.57/1.96  tff(f_95, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((((~v1_xboole_0(B) & v2_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A))), B, k1_tarski(k1_xboole_0)) = k2_yellow19(A, k3_yellow19(A, k2_struct_0(A), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_yellow19)).
% 3.57/1.96  tff(f_52, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 3.57/1.96  tff(f_54, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 3.57/1.96  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 3.57/1.96  tff(f_50, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.57/1.96  tff(f_48, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 3.57/1.96  tff(f_64, axiom, (![A, B]: (~(A = B) => r1_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_zfmisc_1)).
% 3.57/1.96  tff(f_59, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 3.57/1.96  tff(f_116, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (((((~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(k3_yellow_1(A)))) & v2_waybel_0(B, k3_yellow_1(A))) & v13_waybel_0(B, k3_yellow_1(A))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(A))))) => (![C]: ~(r2_hidden(C, B) & v1_xboole_0(C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_yellow19)).
% 3.57/1.96  tff(f_76, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(k2_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc5_struct_0)).
% 3.57/1.96  tff(c_48, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_136])).
% 3.57/1.96  tff(c_46, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_136])).
% 3.57/1.96  tff(c_42, plain, (v1_subset_1('#skF_3', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_136])).
% 3.57/1.96  tff(c_40, plain, (v2_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_136])).
% 3.57/1.96  tff(c_38, plain, (v13_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_136])).
% 3.57/1.96  tff(c_36, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2')))))), inference(cnfTransformation, [status(thm)], [f_136])).
% 3.57/1.96  tff(c_44, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_136])).
% 3.57/1.96  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_30])).
% 3.57/1.96  tff(c_222, plain, (![A_63, B_64, C_65]: (k7_subset_1(A_63, B_64, C_65)=k4_xboole_0(B_64, C_65) | ~m1_subset_1(B_64, k1_zfmisc_1(A_63)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.57/1.96  tff(c_225, plain, (![C_65]: (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2'))), '#skF_3', C_65)=k4_xboole_0('#skF_3', C_65))), inference(resolution, [status(thm)], [c_36, c_222])).
% 3.57/1.96  tff(c_318, plain, (![A_86, B_87]: (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_86))), B_87, k1_tarski(k1_xboole_0))=k2_yellow19(A_86, k3_yellow19(A_86, k2_struct_0(A_86), B_87)) | ~m1_subset_1(B_87, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_86))))) | ~v13_waybel_0(B_87, k3_yellow_1(k2_struct_0(A_86))) | ~v2_waybel_0(B_87, k3_yellow_1(k2_struct_0(A_86))) | v1_xboole_0(B_87) | ~l1_struct_0(A_86) | v2_struct_0(A_86))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.57/1.96  tff(c_320, plain, (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2'))), '#skF_3', k1_tarski(k1_xboole_0))=k2_yellow19('#skF_2', k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | ~v13_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | ~v2_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | v1_xboole_0('#skF_3') | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_36, c_318])).
% 3.57/1.96  tff(c_323, plain, (k2_yellow19('#skF_2', k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'))=k4_xboole_0('#skF_3', k1_tarski(k1_xboole_0)) | v1_xboole_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_40, c_38, c_225, c_320])).
% 3.57/1.96  tff(c_324, plain, (k2_yellow19('#skF_2', k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'))=k4_xboole_0('#skF_3', k1_tarski(k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_48, c_44, c_323])).
% 3.57/1.96  tff(c_34, plain, (k2_yellow19('#skF_2', k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'))!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_136])).
% 3.57/1.96  tff(c_459, plain, (k4_xboole_0('#skF_3', k1_tarski(k1_xboole_0))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_324, c_34])).
% 3.57/1.96  tff(c_16, plain, (![A_10]: (k4_xboole_0(A_10, k1_xboole_0)=A_10)), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.57/1.96  tff(c_18, plain, (![A_11]: (r1_xboole_0(A_11, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.57/1.96  tff(c_70, plain, (![A_39, B_40]: (k3_xboole_0(A_39, B_40)=k1_xboole_0 | ~r1_xboole_0(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.57/1.96  tff(c_82, plain, (![A_11]: (k3_xboole_0(A_11, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_70])).
% 3.57/1.96  tff(c_151, plain, (![A_54, B_55]: (k5_xboole_0(A_54, k3_xboole_0(A_54, B_55))=k4_xboole_0(A_54, B_55))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.57/1.96  tff(c_163, plain, (![A_11]: (k5_xboole_0(A_11, k1_xboole_0)=k4_xboole_0(A_11, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_82, c_151])).
% 3.57/1.96  tff(c_166, plain, (![A_11]: (k5_xboole_0(A_11, k1_xboole_0)=A_11)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_163])).
% 3.57/1.96  tff(c_108, plain, (![A_48, B_49]: (r2_hidden('#skF_1'(A_48, B_49), B_49) | r1_xboole_0(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.57/1.96  tff(c_22, plain, (![A_14, B_15]: (r1_xboole_0(k1_tarski(A_14), k1_tarski(B_15)) | B_15=A_14)), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.57/1.96  tff(c_91, plain, (![A_43, B_44]: (~r2_hidden(A_43, B_44) | ~r1_xboole_0(k1_tarski(A_43), B_44))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.57/1.96  tff(c_103, plain, (![A_14, B_15]: (~r2_hidden(A_14, k1_tarski(B_15)) | B_15=A_14)), inference(resolution, [status(thm)], [c_22, c_91])).
% 3.57/1.96  tff(c_236, plain, (![A_68, B_69]: ('#skF_1'(A_68, k1_tarski(B_69))=B_69 | r1_xboole_0(A_68, k1_tarski(B_69)))), inference(resolution, [status(thm)], [c_108, c_103])).
% 3.57/1.96  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.57/1.96  tff(c_346, plain, (![A_90, B_91]: (k3_xboole_0(A_90, k1_tarski(B_91))=k1_xboole_0 | '#skF_1'(A_90, k1_tarski(B_91))=B_91)), inference(resolution, [status(thm)], [c_236, c_2])).
% 3.57/1.96  tff(c_14, plain, (![A_8, B_9]: (k5_xboole_0(A_8, k3_xboole_0(A_8, B_9))=k4_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.57/1.96  tff(c_360, plain, (![A_90, B_91]: (k4_xboole_0(A_90, k1_tarski(B_91))=k5_xboole_0(A_90, k1_xboole_0) | '#skF_1'(A_90, k1_tarski(B_91))=B_91)), inference(superposition, [status(thm), theory('equality')], [c_346, c_14])).
% 3.57/1.96  tff(c_378, plain, (![A_90, B_91]: (k4_xboole_0(A_90, k1_tarski(B_91))=A_90 | '#skF_1'(A_90, k1_tarski(B_91))=B_91)), inference(demodulation, [status(thm), theory('equality')], [c_166, c_360])).
% 3.57/1.96  tff(c_467, plain, ('#skF_1'('#skF_3', k1_tarski(k1_xboole_0))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_378, c_459])).
% 3.57/1.96  tff(c_12, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.57/1.96  tff(c_471, plain, (r2_hidden(k1_xboole_0, '#skF_3') | r1_xboole_0('#skF_3', k1_tarski(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_467, c_12])).
% 3.57/1.96  tff(c_478, plain, (r1_xboole_0('#skF_3', k1_tarski(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_471])).
% 3.57/1.96  tff(c_485, plain, (k3_xboole_0('#skF_3', k1_tarski(k1_xboole_0))=k1_xboole_0), inference(resolution, [status(thm)], [c_478, c_2])).
% 3.57/1.96  tff(c_493, plain, (k4_xboole_0('#skF_3', k1_tarski(k1_xboole_0))=k5_xboole_0('#skF_3', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_485, c_14])).
% 3.57/1.96  tff(c_501, plain, (k4_xboole_0('#skF_3', k1_tarski(k1_xboole_0))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_166, c_493])).
% 3.57/1.96  tff(c_503, plain, $false, inference(negUnitSimplification, [status(thm)], [c_459, c_501])).
% 3.57/1.96  tff(c_504, plain, (r2_hidden(k1_xboole_0, '#skF_3')), inference(splitRight, [status(thm)], [c_471])).
% 3.57/1.96  tff(c_32, plain, (![C_30, B_28, A_24]: (~v1_xboole_0(C_30) | ~r2_hidden(C_30, B_28) | ~m1_subset_1(B_28, k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_24)))) | ~v13_waybel_0(B_28, k3_yellow_1(A_24)) | ~v2_waybel_0(B_28, k3_yellow_1(A_24)) | ~v1_subset_1(B_28, u1_struct_0(k3_yellow_1(A_24))) | v1_xboole_0(B_28) | v1_xboole_0(A_24))), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.57/1.96  tff(c_509, plain, (![A_24]: (~v1_xboole_0(k1_xboole_0) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_24)))) | ~v13_waybel_0('#skF_3', k3_yellow_1(A_24)) | ~v2_waybel_0('#skF_3', k3_yellow_1(A_24)) | ~v1_subset_1('#skF_3', u1_struct_0(k3_yellow_1(A_24))) | v1_xboole_0('#skF_3') | v1_xboole_0(A_24))), inference(resolution, [status(thm)], [c_504, c_32])).
% 3.57/1.96  tff(c_513, plain, (![A_24]: (~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_24)))) | ~v13_waybel_0('#skF_3', k3_yellow_1(A_24)) | ~v2_waybel_0('#skF_3', k3_yellow_1(A_24)) | ~v1_subset_1('#skF_3', u1_struct_0(k3_yellow_1(A_24))) | v1_xboole_0('#skF_3') | v1_xboole_0(A_24))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_509])).
% 3.57/1.96  tff(c_569, plain, (![A_100]: (~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_100)))) | ~v13_waybel_0('#skF_3', k3_yellow_1(A_100)) | ~v2_waybel_0('#skF_3', k3_yellow_1(A_100)) | ~v1_subset_1('#skF_3', u1_struct_0(k3_yellow_1(A_100))) | v1_xboole_0(A_100))), inference(negUnitSimplification, [status(thm)], [c_44, c_513])).
% 3.57/1.96  tff(c_572, plain, (~v13_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | ~v2_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | ~v1_subset_1('#skF_3', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2')))) | v1_xboole_0(k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_36, c_569])).
% 3.57/1.96  tff(c_575, plain, (v1_xboole_0(k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_572])).
% 3.57/1.96  tff(c_26, plain, (![A_19]: (~v1_xboole_0(k2_struct_0(A_19)) | ~l1_struct_0(A_19) | v2_struct_0(A_19))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.57/1.96  tff(c_578, plain, (~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_575, c_26])).
% 3.57/1.96  tff(c_581, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_578])).
% 3.57/1.96  tff(c_583, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_581])).
% 3.57/1.96  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.57/1.96  
% 3.57/1.96  Inference rules
% 3.57/1.96  ----------------------
% 3.57/1.96  #Ref     : 0
% 3.57/1.96  #Sup     : 123
% 3.57/1.96  #Fact    : 0
% 3.57/1.96  #Define  : 0
% 3.57/1.96  #Split   : 1
% 3.57/1.96  #Chain   : 0
% 3.57/1.96  #Close   : 0
% 3.57/1.96  
% 3.57/1.96  Ordering : KBO
% 3.57/1.96  
% 3.57/1.96  Simplification rules
% 3.57/1.96  ----------------------
% 3.57/1.96  #Subsume      : 12
% 3.57/1.96  #Demod        : 23
% 3.57/1.96  #Tautology    : 59
% 3.57/1.96  #SimpNegUnit  : 6
% 3.57/1.96  #BackRed      : 1
% 3.57/1.96  
% 3.57/1.96  #Partial instantiations: 0
% 3.57/1.96  #Strategies tried      : 1
% 3.57/1.96  
% 3.57/1.96  Timing (in seconds)
% 3.57/1.96  ----------------------
% 3.57/1.96  Preprocessing        : 0.54
% 3.57/1.96  Parsing              : 0.28
% 3.57/1.96  CNF conversion       : 0.04
% 3.57/1.96  Main loop            : 0.47
% 3.57/1.96  Inferencing          : 0.19
% 3.57/1.96  Reduction            : 0.14
% 3.57/1.96  Demodulation         : 0.10
% 3.57/1.96  BG Simplification    : 0.03
% 3.57/1.96  Subsumption          : 0.09
% 3.57/1.96  Abstraction          : 0.03
% 3.57/1.96  MUC search           : 0.00
% 3.57/1.96  Cooper               : 0.00
% 3.57/1.96  Total                : 1.07
% 3.57/1.97  Index Insertion      : 0.00
% 3.57/1.97  Index Deletion       : 0.00
% 3.57/1.97  Index Matching       : 0.00
% 3.57/1.97  BG Taut test         : 0.00
%------------------------------------------------------------------------------
