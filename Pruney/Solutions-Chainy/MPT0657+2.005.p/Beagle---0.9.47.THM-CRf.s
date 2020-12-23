%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:04 EST 2020

% Result     : Theorem 7.67s
% Output     : CNFRefutation 7.67s
% Verified   : 
% Statistics : Number of formulae       :  157 (2575 expanded)
%              Number of leaves         :   33 ( 925 expanded)
%              Depth                    :   27
%              Number of atoms          :  332 (7335 expanded)
%              Number of equality atoms :  101 (2563 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k1_funct_1 > #nlpp > k6_relat_1 > k2_subset_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_136,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B] :
            ( ( v1_relat_1(B)
              & v1_funct_1(B) )
           => ( ( v2_funct_1(A)
                & k2_relat_1(B) = k1_relat_1(A)
                & k5_relat_1(B,A) = k6_relat_1(k2_relat_1(A)) )
             => B = k2_funct_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_1)).

tff(f_68,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( B = k6_relat_1(A)
      <=> ( k1_relat_1(B) = A
          & ! [C] :
              ( r2_hidden(C,A)
             => k1_funct_1(B,C) = C ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_funct_1)).

tff(f_56,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(k6_relat_1(k1_relat_1(A)),A) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_relat_1)).

tff(f_27,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_29,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k2_relat_1(A),k1_relat_1(B))
           => k1_relat_1(k5_relat_1(A,B)) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_relat_1)).

tff(f_118,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_52,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => k5_relat_1(k5_relat_1(A,B),C) = k5_relat_1(A,k5_relat_1(B,C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).

tff(f_64,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_108,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_98,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( v2_funct_1(k5_relat_1(B,A))
              & k2_relat_1(B) = k1_relat_1(A) )
           => ( v2_funct_1(B)
              & v2_funct_1(A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_funct_1)).

tff(c_44,plain,(
    k2_funct_1('#skF_2') != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_58,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_56,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_50,plain,(
    v2_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_54,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_52,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_46,plain,(
    k6_relat_1(k2_relat_1('#skF_2')) = k5_relat_1('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_20,plain,(
    ! [A_17] : v1_relat_1(k6_relat_1(A_17)) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_22,plain,(
    ! [A_17] : v1_funct_1(k6_relat_1(A_17)) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_30,plain,(
    ! [A_18] :
      ( k1_relat_1(k6_relat_1(A_18)) = A_18
      | ~ v1_funct_1(k6_relat_1(A_18))
      | ~ v1_relat_1(k6_relat_1(A_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_60,plain,(
    ! [A_18] :
      ( k1_relat_1(k6_relat_1(A_18)) = A_18
      | ~ v1_relat_1(k6_relat_1(A_18)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_30])).

tff(c_64,plain,(
    ! [A_18] : k1_relat_1(k6_relat_1(A_18)) = A_18 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_60])).

tff(c_121,plain,(
    ! [A_41] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(A_41)),A_41) = A_41
      | ~ v1_relat_1(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_133,plain,(
    ! [A_18] :
      ( k5_relat_1(k6_relat_1(A_18),k6_relat_1(A_18)) = k6_relat_1(A_18)
      | ~ v1_relat_1(k6_relat_1(A_18)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_121])).

tff(c_140,plain,(
    ! [A_42] : k5_relat_1(k6_relat_1(A_42),k6_relat_1(A_42)) = k6_relat_1(A_42) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_133])).

tff(c_152,plain,(
    k5_relat_1(k6_relat_1(k2_relat_1('#skF_2')),k5_relat_1('#skF_3','#skF_2')) = k6_relat_1(k2_relat_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_140])).

tff(c_156,plain,(
    k5_relat_1(k5_relat_1('#skF_3','#skF_2'),k5_relat_1('#skF_3','#skF_2')) = k5_relat_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_46,c_152])).

tff(c_96,plain,(
    k1_relat_1(k5_relat_1('#skF_3','#skF_2')) = k2_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_64])).

tff(c_2,plain,(
    ! [A_1] : k2_subset_1(A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2] : m1_subset_1(k2_subset_1(A_2),k1_zfmisc_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_67,plain,(
    ! [A_2] : m1_subset_1(A_2,k1_zfmisc_1(A_2)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_4])).

tff(c_109,plain,(
    ! [A_35,B_36] :
      ( r1_tarski(A_35,B_36)
      | ~ m1_subset_1(A_35,k1_zfmisc_1(B_36)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_113,plain,(
    ! [A_2] : r1_tarski(A_2,A_2) ),
    inference(resolution,[status(thm)],[c_67,c_109])).

tff(c_48,plain,(
    k2_relat_1('#skF_3') = k1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_215,plain,(
    ! [A_50,B_51] :
      ( k1_relat_1(k5_relat_1(A_50,B_51)) = k1_relat_1(A_50)
      | ~ r1_tarski(k2_relat_1(A_50),k1_relat_1(B_51))
      | ~ v1_relat_1(B_51)
      | ~ v1_relat_1(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_230,plain,(
    ! [B_51] :
      ( k1_relat_1(k5_relat_1('#skF_3',B_51)) = k1_relat_1('#skF_3')
      | ~ r1_tarski(k1_relat_1('#skF_2'),k1_relat_1(B_51))
      | ~ v1_relat_1(B_51)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_215])).

tff(c_272,plain,(
    ! [B_54] :
      ( k1_relat_1(k5_relat_1('#skF_3',B_54)) = k1_relat_1('#skF_3')
      | ~ r1_tarski(k1_relat_1('#skF_2'),k1_relat_1(B_54))
      | ~ v1_relat_1(B_54) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_230])).

tff(c_282,plain,
    ( k1_relat_1(k5_relat_1('#skF_3','#skF_2')) = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_113,c_272])).

tff(c_291,plain,(
    k2_relat_1('#skF_2') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_96,c_282])).

tff(c_331,plain,(
    k6_relat_1(k1_relat_1('#skF_3')) = k5_relat_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_291,c_46])).

tff(c_42,plain,(
    ! [A_27] :
      ( k5_relat_1(A_27,k2_funct_1(A_27)) = k6_relat_1(k1_relat_1(A_27))
      | ~ v2_funct_1(A_27)
      | ~ v1_funct_1(A_27)
      | ~ v1_relat_1(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_100,plain,(
    v1_relat_1(k5_relat_1('#skF_3','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_20])).

tff(c_14,plain,(
    ! [A_15] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(A_15)),A_15) = A_15
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_385,plain,
    ( k5_relat_1(k5_relat_1('#skF_3','#skF_2'),'#skF_3') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_331,c_14])).

tff(c_398,plain,(
    k5_relat_1(k5_relat_1('#skF_3','#skF_2'),'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_385])).

tff(c_454,plain,(
    ! [A_58,B_59,C_60] :
      ( k5_relat_1(k5_relat_1(A_58,B_59),C_60) = k5_relat_1(A_58,k5_relat_1(B_59,C_60))
      | ~ v1_relat_1(C_60)
      | ~ v1_relat_1(B_59)
      | ~ v1_relat_1(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_483,plain,(
    ! [C_60] :
      ( k5_relat_1(k5_relat_1('#skF_3','#skF_2'),k5_relat_1('#skF_3',C_60)) = k5_relat_1('#skF_3',C_60)
      | ~ v1_relat_1(C_60)
      | ~ v1_relat_1('#skF_3')
      | ~ v1_relat_1(k5_relat_1('#skF_3','#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_398,c_454])).

tff(c_591,plain,(
    ! [C_62] :
      ( k5_relat_1(k5_relat_1('#skF_3','#skF_2'),k5_relat_1('#skF_3',C_62)) = k5_relat_1('#skF_3',C_62)
      | ~ v1_relat_1(C_62) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_54,c_483])).

tff(c_619,plain,
    ( k5_relat_1(k5_relat_1('#skF_3','#skF_2'),k6_relat_1(k1_relat_1('#skF_3'))) = k5_relat_1('#skF_3',k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_591])).

tff(c_637,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k5_relat_1('#skF_3','#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_156,c_331,c_619])).

tff(c_641,plain,(
    ~ v2_funct_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_637])).

tff(c_139,plain,(
    ! [A_18] : k5_relat_1(k6_relat_1(A_18),k6_relat_1(A_18)) = k6_relat_1(A_18) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_133])).

tff(c_505,plain,(
    ! [A_18,C_60] :
      ( k5_relat_1(k6_relat_1(A_18),k5_relat_1(k6_relat_1(A_18),C_60)) = k5_relat_1(k6_relat_1(A_18),C_60)
      | ~ v1_relat_1(C_60)
      | ~ v1_relat_1(k6_relat_1(A_18))
      | ~ v1_relat_1(k6_relat_1(A_18)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_139,c_454])).

tff(c_674,plain,(
    ! [A_64,C_65] :
      ( k5_relat_1(k6_relat_1(A_64),k5_relat_1(k6_relat_1(A_64),C_65)) = k5_relat_1(k6_relat_1(A_64),C_65)
      | ~ v1_relat_1(C_65) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_20,c_505])).

tff(c_699,plain,(
    ! [A_64] :
      ( k5_relat_1(k6_relat_1(A_64),k6_relat_1(k1_relat_1(k6_relat_1(A_64)))) = k5_relat_1(k6_relat_1(A_64),k2_funct_1(k6_relat_1(A_64)))
      | ~ v1_relat_1(k2_funct_1(k6_relat_1(A_64)))
      | ~ v2_funct_1(k6_relat_1(A_64))
      | ~ v1_funct_1(k6_relat_1(A_64))
      | ~ v1_relat_1(k6_relat_1(A_64)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_674])).

tff(c_1071,plain,(
    ! [A_73] :
      ( k5_relat_1(k6_relat_1(A_73),k2_funct_1(k6_relat_1(A_73))) = k6_relat_1(A_73)
      | ~ v1_relat_1(k2_funct_1(k6_relat_1(A_73)))
      | ~ v2_funct_1(k6_relat_1(A_73)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_22,c_139,c_64,c_699])).

tff(c_1095,plain,
    ( k5_relat_1(k5_relat_1('#skF_3','#skF_2'),k2_funct_1(k6_relat_1(k1_relat_1('#skF_3')))) = k6_relat_1(k1_relat_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1(k6_relat_1(k1_relat_1('#skF_3'))))
    | ~ v2_funct_1(k6_relat_1(k1_relat_1('#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_331,c_1071])).

tff(c_1113,plain,
    ( k5_relat_1(k5_relat_1('#skF_3','#skF_2'),k2_funct_1(k5_relat_1('#skF_3','#skF_2'))) = k5_relat_1('#skF_3','#skF_2')
    | ~ v1_relat_1(k2_funct_1(k5_relat_1('#skF_3','#skF_2')))
    | ~ v2_funct_1(k5_relat_1('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_331,c_331,c_331,c_331,c_1095])).

tff(c_1221,plain,(
    ~ v2_funct_1(k5_relat_1('#skF_3','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_1113])).

tff(c_98,plain,(
    v1_funct_1(k5_relat_1('#skF_3','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_22])).

tff(c_330,plain,(
    k1_relat_1(k5_relat_1('#skF_3','#skF_2')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_291,c_96])).

tff(c_18,plain,(
    ! [A_16] :
      ( v1_relat_1(k2_funct_1(A_16))
      | ~ v1_funct_1(A_16)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_185,plain,(
    ! [A_47] :
      ( k1_relat_1(k2_funct_1(A_47)) = k2_relat_1(A_47)
      | ~ v2_funct_1(A_47)
      | ~ v1_funct_1(A_47)
      | ~ v1_relat_1(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_3941,plain,(
    ! [A_112] :
      ( k5_relat_1(k6_relat_1(k2_relat_1(A_112)),k2_funct_1(A_112)) = k2_funct_1(A_112)
      | ~ v1_relat_1(k2_funct_1(A_112))
      | ~ v2_funct_1(A_112)
      | ~ v1_funct_1(A_112)
      | ~ v1_relat_1(A_112) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_185,c_14])).

tff(c_3965,plain,
    ( k5_relat_1(k6_relat_1(k1_relat_1('#skF_3')),k2_funct_1('#skF_2')) = k2_funct_1('#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_2'))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_291,c_3941])).

tff(c_3984,plain,
    ( k5_relat_1(k5_relat_1('#skF_3','#skF_2'),k2_funct_1('#skF_2')) = k2_funct_1('#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_50,c_331,c_3965])).

tff(c_3987,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_3984])).

tff(c_3990,plain,
    ( ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_18,c_3987])).

tff(c_3994,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_3990])).

tff(c_3996,plain,(
    v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_3984])).

tff(c_3995,plain,(
    k5_relat_1(k5_relat_1('#skF_3','#skF_2'),k2_funct_1('#skF_2')) = k2_funct_1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_3984])).

tff(c_12,plain,(
    ! [A_8,B_12,C_14] :
      ( k5_relat_1(k5_relat_1(A_8,B_12),C_14) = k5_relat_1(A_8,k5_relat_1(B_12,C_14))
      | ~ v1_relat_1(C_14)
      | ~ v1_relat_1(B_12)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_4029,plain,
    ( k5_relat_1('#skF_3',k5_relat_1('#skF_2',k2_funct_1('#skF_2'))) = k2_funct_1('#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_2'))
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3995,c_12])).

tff(c_4047,plain,(
    k5_relat_1('#skF_3',k5_relat_1('#skF_2',k2_funct_1('#skF_2'))) = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_58,c_3996,c_4029])).

tff(c_4073,plain,
    ( k5_relat_1('#skF_3',k6_relat_1(k1_relat_1('#skF_2'))) = k2_funct_1('#skF_2')
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_4047])).

tff(c_4089,plain,(
    k5_relat_1('#skF_3',k6_relat_1(k1_relat_1('#skF_2'))) = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_50,c_4073])).

tff(c_4108,plain,(
    ! [C_14] :
      ( k5_relat_1('#skF_3',k5_relat_1(k6_relat_1(k1_relat_1('#skF_2')),C_14)) = k5_relat_1(k2_funct_1('#skF_2'),C_14)
      | ~ v1_relat_1(C_14)
      | ~ v1_relat_1(k6_relat_1(k1_relat_1('#skF_2')))
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4089,c_12])).

tff(c_4309,plain,(
    ! [C_117] :
      ( k5_relat_1('#skF_3',k5_relat_1(k6_relat_1(k1_relat_1('#skF_2')),C_117)) = k5_relat_1(k2_funct_1('#skF_2'),C_117)
      | ~ v1_relat_1(C_117) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_20,c_4108])).

tff(c_4354,plain,
    ( k5_relat_1(k2_funct_1('#skF_2'),'#skF_2') = k5_relat_1('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_4309])).

tff(c_4374,plain,(
    k5_relat_1(k2_funct_1('#skF_2'),'#skF_2') = k5_relat_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_58,c_4354])).

tff(c_288,plain,(
    ! [A_18] :
      ( k1_relat_1(k5_relat_1('#skF_3',k6_relat_1(A_18))) = k1_relat_1('#skF_3')
      | ~ r1_tarski(k1_relat_1('#skF_2'),A_18)
      | ~ v1_relat_1(k6_relat_1(A_18)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_272])).

tff(c_295,plain,(
    ! [A_18] :
      ( k1_relat_1(k5_relat_1('#skF_3',k6_relat_1(A_18))) = k1_relat_1('#skF_3')
      | ~ r1_tarski(k1_relat_1('#skF_2'),A_18) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_288])).

tff(c_4105,plain,
    ( k1_relat_1(k2_funct_1('#skF_2')) = k1_relat_1('#skF_3')
    | ~ r1_tarski(k1_relat_1('#skF_2'),k1_relat_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4089,c_295])).

tff(c_4124,plain,(
    k1_relat_1(k2_funct_1('#skF_2')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_4105])).

tff(c_10,plain,(
    ! [A_5,B_7] :
      ( k1_relat_1(k5_relat_1(A_5,B_7)) = k1_relat_1(A_5)
      | ~ r1_tarski(k2_relat_1(A_5),k1_relat_1(B_7))
      | ~ v1_relat_1(B_7)
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_335,plain,(
    ! [B_7] :
      ( k1_relat_1(k5_relat_1('#skF_2',B_7)) = k1_relat_1('#skF_2')
      | ~ r1_tarski(k1_relat_1('#skF_3'),k1_relat_1(B_7))
      | ~ v1_relat_1(B_7)
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_291,c_10])).

tff(c_339,plain,(
    ! [B_7] :
      ( k1_relat_1(k5_relat_1('#skF_2',B_7)) = k1_relat_1('#skF_2')
      | ~ r1_tarski(k1_relat_1('#skF_3'),k1_relat_1(B_7))
      | ~ v1_relat_1(B_7) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_335])).

tff(c_4139,plain,
    ( k1_relat_1(k5_relat_1('#skF_2',k2_funct_1('#skF_2'))) = k1_relat_1('#skF_2')
    | ~ r1_tarski(k1_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4124,c_339])).

tff(c_4172,plain,(
    k1_relat_1(k5_relat_1('#skF_2',k2_funct_1('#skF_2'))) = k1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3996,c_113,c_4139])).

tff(c_4250,plain,
    ( k5_relat_1(k6_relat_1(k1_relat_1('#skF_2')),k5_relat_1('#skF_2',k2_funct_1('#skF_2'))) = k5_relat_1('#skF_2',k2_funct_1('#skF_2'))
    | ~ v1_relat_1(k5_relat_1('#skF_2',k2_funct_1('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_4172,c_14])).

tff(c_6118,plain,(
    ~ v1_relat_1(k5_relat_1('#skF_2',k2_funct_1('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_4250])).

tff(c_6121,plain,
    ( ~ v1_relat_1(k6_relat_1(k1_relat_1('#skF_2')))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_6118])).

tff(c_6124,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_50,c_20,c_6121])).

tff(c_6125,plain,(
    k5_relat_1(k6_relat_1(k1_relat_1('#skF_2')),k5_relat_1('#skF_2',k2_funct_1('#skF_2'))) = k5_relat_1('#skF_2',k2_funct_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_4250])).

tff(c_6178,plain,
    ( k5_relat_1(k6_relat_1(k1_relat_1('#skF_2')),k6_relat_1(k1_relat_1('#skF_2'))) = k5_relat_1('#skF_2',k2_funct_1('#skF_2'))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_6125])).

tff(c_6208,plain,(
    k5_relat_1('#skF_2',k2_funct_1('#skF_2')) = k6_relat_1(k1_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_50,c_139,c_6178])).

tff(c_6249,plain,(
    ! [C_14] :
      ( k5_relat_1(k6_relat_1(k1_relat_1('#skF_2')),C_14) = k5_relat_1('#skF_2',k5_relat_1(k2_funct_1('#skF_2'),C_14))
      | ~ v1_relat_1(C_14)
      | ~ v1_relat_1(k2_funct_1('#skF_2'))
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6208,c_12])).

tff(c_6314,plain,(
    ! [C_142] :
      ( k5_relat_1(k6_relat_1(k1_relat_1('#skF_2')),C_142) = k5_relat_1('#skF_2',k5_relat_1(k2_funct_1('#skF_2'),C_142))
      | ~ v1_relat_1(C_142) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_3996,c_6249])).

tff(c_6392,plain,
    ( k5_relat_1('#skF_2',k5_relat_1(k2_funct_1('#skF_2'),'#skF_2')) = '#skF_2'
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_6314,c_14])).

tff(c_6462,plain,(
    k5_relat_1('#skF_2',k5_relat_1('#skF_3','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_58,c_4374,c_6392])).

tff(c_32,plain,(
    ! [A_23,B_25] :
      ( v2_funct_1(A_23)
      | k2_relat_1(B_25) != k1_relat_1(A_23)
      | ~ v2_funct_1(k5_relat_1(B_25,A_23))
      | ~ v1_funct_1(B_25)
      | ~ v1_relat_1(B_25)
      | ~ v1_funct_1(A_23)
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_6567,plain,
    ( v2_funct_1(k5_relat_1('#skF_3','#skF_2'))
    | k1_relat_1(k5_relat_1('#skF_3','#skF_2')) != k2_relat_1('#skF_2')
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_funct_1(k5_relat_1('#skF_3','#skF_2'))
    | ~ v1_relat_1(k5_relat_1('#skF_3','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_6462,c_32])).

tff(c_6592,plain,(
    v2_funct_1(k5_relat_1('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_98,c_58,c_56,c_50,c_291,c_330,c_6567])).

tff(c_6594,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1221,c_6592])).

tff(c_6596,plain,(
    v2_funct_1(k5_relat_1('#skF_3','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_1113])).

tff(c_34,plain,(
    ! [B_25,A_23] :
      ( v2_funct_1(B_25)
      | k2_relat_1(B_25) != k1_relat_1(A_23)
      | ~ v2_funct_1(k5_relat_1(B_25,A_23))
      | ~ v1_funct_1(B_25)
      | ~ v1_relat_1(B_25)
      | ~ v1_funct_1(A_23)
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_6599,plain,
    ( v2_funct_1('#skF_3')
    | k2_relat_1('#skF_3') != k1_relat_1('#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_6596,c_34])).

tff(c_6605,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_52,c_48,c_6599])).

tff(c_6607,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_641,c_6605])).

tff(c_6609,plain,(
    v2_funct_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_637])).

tff(c_40,plain,(
    ! [A_27] :
      ( k5_relat_1(k2_funct_1(A_27),A_27) = k6_relat_1(k2_relat_1(A_27))
      | ~ v2_funct_1(A_27)
      | ~ v1_funct_1(A_27)
      | ~ v1_relat_1(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_6608,plain,
    ( ~ v1_relat_1(k2_funct_1('#skF_3'))
    | k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k5_relat_1('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_637])).

tff(c_6610,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_6608])).

tff(c_6613,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_6610])).

tff(c_6617,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_6613])).

tff(c_6619,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_6608])).

tff(c_6618,plain,(
    k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k5_relat_1('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_6608])).

tff(c_6657,plain,(
    ! [C_14] :
      ( k5_relat_1('#skF_3',k5_relat_1(k2_funct_1('#skF_3'),C_14)) = k5_relat_1(k5_relat_1('#skF_3','#skF_2'),C_14)
      | ~ v1_relat_1(C_14)
      | ~ v1_relat_1(k2_funct_1('#skF_3'))
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6618,c_12])).

tff(c_6889,plain,(
    ! [C_151] :
      ( k5_relat_1('#skF_3',k5_relat_1(k2_funct_1('#skF_3'),C_151)) = k5_relat_1(k5_relat_1('#skF_3','#skF_2'),C_151)
      | ~ v1_relat_1(C_151) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_6619,c_6657])).

tff(c_6912,plain,
    ( k5_relat_1('#skF_3',k6_relat_1(k2_relat_1('#skF_3'))) = k5_relat_1(k5_relat_1('#skF_3','#skF_2'),'#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_6889])).

tff(c_6922,plain,(
    k5_relat_1('#skF_3',k6_relat_1(k1_relat_1('#skF_2'))) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_6609,c_54,c_48,c_398,c_6912])).

tff(c_7682,plain,(
    ! [A_162] :
      ( k5_relat_1(k6_relat_1(k2_relat_1(A_162)),k2_funct_1(A_162)) = k2_funct_1(A_162)
      | ~ v1_relat_1(k2_funct_1(A_162))
      | ~ v2_funct_1(A_162)
      | ~ v1_funct_1(A_162)
      | ~ v1_relat_1(A_162) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_185,c_14])).

tff(c_7710,plain,
    ( k5_relat_1(k6_relat_1(k1_relat_1('#skF_3')),k2_funct_1('#skF_2')) = k2_funct_1('#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_2'))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_291,c_7682])).

tff(c_7731,plain,
    ( k5_relat_1(k5_relat_1('#skF_3','#skF_2'),k2_funct_1('#skF_2')) = k2_funct_1('#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_50,c_331,c_7710])).

tff(c_7734,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_7731])).

tff(c_7737,plain,
    ( ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_18,c_7734])).

tff(c_7741,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_7737])).

tff(c_7743,plain,(
    v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_7731])).

tff(c_7742,plain,(
    k5_relat_1(k5_relat_1('#skF_3','#skF_2'),k2_funct_1('#skF_2')) = k2_funct_1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_7731])).

tff(c_7762,plain,
    ( k5_relat_1('#skF_3',k5_relat_1('#skF_2',k2_funct_1('#skF_2'))) = k2_funct_1('#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_2'))
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_7742,c_12])).

tff(c_7780,plain,(
    k5_relat_1('#skF_3',k5_relat_1('#skF_2',k2_funct_1('#skF_2'))) = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_58,c_7743,c_7762])).

tff(c_7803,plain,
    ( k5_relat_1('#skF_3',k6_relat_1(k1_relat_1('#skF_2'))) = k2_funct_1('#skF_2')
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_7780])).

tff(c_7816,plain,(
    k2_funct_1('#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_50,c_6922,c_7803])).

tff(c_7818,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_7816])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n006.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 15:32:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.67/2.62  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.67/2.63  
% 7.67/2.63  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.67/2.64  %$ r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k1_funct_1 > #nlpp > k6_relat_1 > k2_subset_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 7.67/2.64  
% 7.67/2.64  %Foreground sorts:
% 7.67/2.64  
% 7.67/2.64  
% 7.67/2.64  %Background operators:
% 7.67/2.64  
% 7.67/2.64  
% 7.67/2.64  %Foreground operators:
% 7.67/2.64  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.67/2.64  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 7.67/2.64  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 7.67/2.64  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.67/2.64  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.67/2.64  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 7.67/2.64  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.67/2.64  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.67/2.64  tff('#skF_2', type, '#skF_2': $i).
% 7.67/2.64  tff('#skF_3', type, '#skF_3': $i).
% 7.67/2.64  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.67/2.64  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 7.67/2.64  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.67/2.64  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.67/2.64  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 7.67/2.64  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.67/2.64  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 7.67/2.64  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 7.67/2.64  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.67/2.64  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.67/2.64  
% 7.67/2.66  tff(f_136, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(B) = k1_relat_1(A))) & (k5_relat_1(B, A) = k6_relat_1(k2_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_funct_1)).
% 7.67/2.66  tff(f_68, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 7.67/2.66  tff(f_81, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((B = k6_relat_1(A)) <=> ((k1_relat_1(B) = A) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_funct_1)).
% 7.67/2.66  tff(f_56, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(k6_relat_1(k1_relat_1(A)), A) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t78_relat_1)).
% 7.67/2.66  tff(f_27, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 7.67/2.66  tff(f_29, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 7.67/2.66  tff(f_33, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 7.67/2.66  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(A), k1_relat_1(B)) => (k1_relat_1(k5_relat_1(A, B)) = k1_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_relat_1)).
% 7.67/2.66  tff(f_118, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_1)).
% 7.67/2.66  tff(f_52, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k5_relat_1(k5_relat_1(A, B), C) = k5_relat_1(A, k5_relat_1(B, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_relat_1)).
% 7.67/2.66  tff(f_64, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 7.67/2.66  tff(f_108, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 7.67/2.66  tff(f_98, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(k5_relat_1(B, A)) & (k2_relat_1(B) = k1_relat_1(A))) => (v2_funct_1(B) & v2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_funct_1)).
% 7.67/2.66  tff(c_44, plain, (k2_funct_1('#skF_2')!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_136])).
% 7.67/2.66  tff(c_58, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_136])).
% 7.67/2.66  tff(c_56, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_136])).
% 7.67/2.66  tff(c_50, plain, (v2_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_136])).
% 7.67/2.66  tff(c_54, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_136])).
% 7.67/2.66  tff(c_52, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_136])).
% 7.67/2.66  tff(c_46, plain, (k6_relat_1(k2_relat_1('#skF_2'))=k5_relat_1('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_136])).
% 7.67/2.66  tff(c_20, plain, (![A_17]: (v1_relat_1(k6_relat_1(A_17)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 7.67/2.66  tff(c_22, plain, (![A_17]: (v1_funct_1(k6_relat_1(A_17)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 7.67/2.66  tff(c_30, plain, (![A_18]: (k1_relat_1(k6_relat_1(A_18))=A_18 | ~v1_funct_1(k6_relat_1(A_18)) | ~v1_relat_1(k6_relat_1(A_18)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 7.67/2.66  tff(c_60, plain, (![A_18]: (k1_relat_1(k6_relat_1(A_18))=A_18 | ~v1_relat_1(k6_relat_1(A_18)))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_30])).
% 7.67/2.66  tff(c_64, plain, (![A_18]: (k1_relat_1(k6_relat_1(A_18))=A_18)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_60])).
% 7.67/2.66  tff(c_121, plain, (![A_41]: (k5_relat_1(k6_relat_1(k1_relat_1(A_41)), A_41)=A_41 | ~v1_relat_1(A_41))), inference(cnfTransformation, [status(thm)], [f_56])).
% 7.67/2.66  tff(c_133, plain, (![A_18]: (k5_relat_1(k6_relat_1(A_18), k6_relat_1(A_18))=k6_relat_1(A_18) | ~v1_relat_1(k6_relat_1(A_18)))), inference(superposition, [status(thm), theory('equality')], [c_64, c_121])).
% 7.67/2.66  tff(c_140, plain, (![A_42]: (k5_relat_1(k6_relat_1(A_42), k6_relat_1(A_42))=k6_relat_1(A_42))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_133])).
% 7.67/2.66  tff(c_152, plain, (k5_relat_1(k6_relat_1(k2_relat_1('#skF_2')), k5_relat_1('#skF_3', '#skF_2'))=k6_relat_1(k2_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_46, c_140])).
% 7.67/2.66  tff(c_156, plain, (k5_relat_1(k5_relat_1('#skF_3', '#skF_2'), k5_relat_1('#skF_3', '#skF_2'))=k5_relat_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_46, c_152])).
% 7.67/2.66  tff(c_96, plain, (k1_relat_1(k5_relat_1('#skF_3', '#skF_2'))=k2_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_46, c_64])).
% 7.67/2.66  tff(c_2, plain, (![A_1]: (k2_subset_1(A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.67/2.66  tff(c_4, plain, (![A_2]: (m1_subset_1(k2_subset_1(A_2), k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.67/2.66  tff(c_67, plain, (![A_2]: (m1_subset_1(A_2, k1_zfmisc_1(A_2)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_4])).
% 7.67/2.66  tff(c_109, plain, (![A_35, B_36]: (r1_tarski(A_35, B_36) | ~m1_subset_1(A_35, k1_zfmisc_1(B_36)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.67/2.66  tff(c_113, plain, (![A_2]: (r1_tarski(A_2, A_2))), inference(resolution, [status(thm)], [c_67, c_109])).
% 7.67/2.66  tff(c_48, plain, (k2_relat_1('#skF_3')=k1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_136])).
% 7.67/2.66  tff(c_215, plain, (![A_50, B_51]: (k1_relat_1(k5_relat_1(A_50, B_51))=k1_relat_1(A_50) | ~r1_tarski(k2_relat_1(A_50), k1_relat_1(B_51)) | ~v1_relat_1(B_51) | ~v1_relat_1(A_50))), inference(cnfTransformation, [status(thm)], [f_42])).
% 7.67/2.66  tff(c_230, plain, (![B_51]: (k1_relat_1(k5_relat_1('#skF_3', B_51))=k1_relat_1('#skF_3') | ~r1_tarski(k1_relat_1('#skF_2'), k1_relat_1(B_51)) | ~v1_relat_1(B_51) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_48, c_215])).
% 7.67/2.66  tff(c_272, plain, (![B_54]: (k1_relat_1(k5_relat_1('#skF_3', B_54))=k1_relat_1('#skF_3') | ~r1_tarski(k1_relat_1('#skF_2'), k1_relat_1(B_54)) | ~v1_relat_1(B_54))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_230])).
% 7.67/2.66  tff(c_282, plain, (k1_relat_1(k5_relat_1('#skF_3', '#skF_2'))=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_113, c_272])).
% 7.67/2.66  tff(c_291, plain, (k2_relat_1('#skF_2')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_96, c_282])).
% 7.67/2.66  tff(c_331, plain, (k6_relat_1(k1_relat_1('#skF_3'))=k5_relat_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_291, c_46])).
% 7.67/2.66  tff(c_42, plain, (![A_27]: (k5_relat_1(A_27, k2_funct_1(A_27))=k6_relat_1(k1_relat_1(A_27)) | ~v2_funct_1(A_27) | ~v1_funct_1(A_27) | ~v1_relat_1(A_27))), inference(cnfTransformation, [status(thm)], [f_118])).
% 7.67/2.66  tff(c_100, plain, (v1_relat_1(k5_relat_1('#skF_3', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_46, c_20])).
% 7.67/2.66  tff(c_14, plain, (![A_15]: (k5_relat_1(k6_relat_1(k1_relat_1(A_15)), A_15)=A_15 | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_56])).
% 7.67/2.66  tff(c_385, plain, (k5_relat_1(k5_relat_1('#skF_3', '#skF_2'), '#skF_3')='#skF_3' | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_331, c_14])).
% 7.67/2.66  tff(c_398, plain, (k5_relat_1(k5_relat_1('#skF_3', '#skF_2'), '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_385])).
% 7.67/2.66  tff(c_454, plain, (![A_58, B_59, C_60]: (k5_relat_1(k5_relat_1(A_58, B_59), C_60)=k5_relat_1(A_58, k5_relat_1(B_59, C_60)) | ~v1_relat_1(C_60) | ~v1_relat_1(B_59) | ~v1_relat_1(A_58))), inference(cnfTransformation, [status(thm)], [f_52])).
% 7.67/2.66  tff(c_483, plain, (![C_60]: (k5_relat_1(k5_relat_1('#skF_3', '#skF_2'), k5_relat_1('#skF_3', C_60))=k5_relat_1('#skF_3', C_60) | ~v1_relat_1(C_60) | ~v1_relat_1('#skF_3') | ~v1_relat_1(k5_relat_1('#skF_3', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_398, c_454])).
% 7.67/2.66  tff(c_591, plain, (![C_62]: (k5_relat_1(k5_relat_1('#skF_3', '#skF_2'), k5_relat_1('#skF_3', C_62))=k5_relat_1('#skF_3', C_62) | ~v1_relat_1(C_62))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_54, c_483])).
% 7.67/2.66  tff(c_619, plain, (k5_relat_1(k5_relat_1('#skF_3', '#skF_2'), k6_relat_1(k1_relat_1('#skF_3')))=k5_relat_1('#skF_3', k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_42, c_591])).
% 7.67/2.66  tff(c_637, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k5_relat_1('#skF_3', '#skF_2') | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_156, c_331, c_619])).
% 7.67/2.66  tff(c_641, plain, (~v2_funct_1('#skF_3')), inference(splitLeft, [status(thm)], [c_637])).
% 7.67/2.66  tff(c_139, plain, (![A_18]: (k5_relat_1(k6_relat_1(A_18), k6_relat_1(A_18))=k6_relat_1(A_18))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_133])).
% 7.67/2.66  tff(c_505, plain, (![A_18, C_60]: (k5_relat_1(k6_relat_1(A_18), k5_relat_1(k6_relat_1(A_18), C_60))=k5_relat_1(k6_relat_1(A_18), C_60) | ~v1_relat_1(C_60) | ~v1_relat_1(k6_relat_1(A_18)) | ~v1_relat_1(k6_relat_1(A_18)))), inference(superposition, [status(thm), theory('equality')], [c_139, c_454])).
% 7.67/2.66  tff(c_674, plain, (![A_64, C_65]: (k5_relat_1(k6_relat_1(A_64), k5_relat_1(k6_relat_1(A_64), C_65))=k5_relat_1(k6_relat_1(A_64), C_65) | ~v1_relat_1(C_65))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_20, c_505])).
% 7.67/2.66  tff(c_699, plain, (![A_64]: (k5_relat_1(k6_relat_1(A_64), k6_relat_1(k1_relat_1(k6_relat_1(A_64))))=k5_relat_1(k6_relat_1(A_64), k2_funct_1(k6_relat_1(A_64))) | ~v1_relat_1(k2_funct_1(k6_relat_1(A_64))) | ~v2_funct_1(k6_relat_1(A_64)) | ~v1_funct_1(k6_relat_1(A_64)) | ~v1_relat_1(k6_relat_1(A_64)))), inference(superposition, [status(thm), theory('equality')], [c_42, c_674])).
% 7.67/2.66  tff(c_1071, plain, (![A_73]: (k5_relat_1(k6_relat_1(A_73), k2_funct_1(k6_relat_1(A_73)))=k6_relat_1(A_73) | ~v1_relat_1(k2_funct_1(k6_relat_1(A_73))) | ~v2_funct_1(k6_relat_1(A_73)))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_22, c_139, c_64, c_699])).
% 7.67/2.66  tff(c_1095, plain, (k5_relat_1(k5_relat_1('#skF_3', '#skF_2'), k2_funct_1(k6_relat_1(k1_relat_1('#skF_3'))))=k6_relat_1(k1_relat_1('#skF_3')) | ~v1_relat_1(k2_funct_1(k6_relat_1(k1_relat_1('#skF_3')))) | ~v2_funct_1(k6_relat_1(k1_relat_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_331, c_1071])).
% 7.67/2.66  tff(c_1113, plain, (k5_relat_1(k5_relat_1('#skF_3', '#skF_2'), k2_funct_1(k5_relat_1('#skF_3', '#skF_2')))=k5_relat_1('#skF_3', '#skF_2') | ~v1_relat_1(k2_funct_1(k5_relat_1('#skF_3', '#skF_2'))) | ~v2_funct_1(k5_relat_1('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_331, c_331, c_331, c_331, c_1095])).
% 7.67/2.66  tff(c_1221, plain, (~v2_funct_1(k5_relat_1('#skF_3', '#skF_2'))), inference(splitLeft, [status(thm)], [c_1113])).
% 7.67/2.66  tff(c_98, plain, (v1_funct_1(k5_relat_1('#skF_3', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_46, c_22])).
% 7.67/2.66  tff(c_330, plain, (k1_relat_1(k5_relat_1('#skF_3', '#skF_2'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_291, c_96])).
% 7.67/2.66  tff(c_18, plain, (![A_16]: (v1_relat_1(k2_funct_1(A_16)) | ~v1_funct_1(A_16) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_64])).
% 7.67/2.66  tff(c_185, plain, (![A_47]: (k1_relat_1(k2_funct_1(A_47))=k2_relat_1(A_47) | ~v2_funct_1(A_47) | ~v1_funct_1(A_47) | ~v1_relat_1(A_47))), inference(cnfTransformation, [status(thm)], [f_108])).
% 7.67/2.66  tff(c_3941, plain, (![A_112]: (k5_relat_1(k6_relat_1(k2_relat_1(A_112)), k2_funct_1(A_112))=k2_funct_1(A_112) | ~v1_relat_1(k2_funct_1(A_112)) | ~v2_funct_1(A_112) | ~v1_funct_1(A_112) | ~v1_relat_1(A_112))), inference(superposition, [status(thm), theory('equality')], [c_185, c_14])).
% 7.67/2.66  tff(c_3965, plain, (k5_relat_1(k6_relat_1(k1_relat_1('#skF_3')), k2_funct_1('#skF_2'))=k2_funct_1('#skF_2') | ~v1_relat_1(k2_funct_1('#skF_2')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_291, c_3941])).
% 7.67/2.66  tff(c_3984, plain, (k5_relat_1(k5_relat_1('#skF_3', '#skF_2'), k2_funct_1('#skF_2'))=k2_funct_1('#skF_2') | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_50, c_331, c_3965])).
% 7.67/2.66  tff(c_3987, plain, (~v1_relat_1(k2_funct_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_3984])).
% 7.67/2.66  tff(c_3990, plain, (~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_18, c_3987])).
% 7.67/2.66  tff(c_3994, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_3990])).
% 7.67/2.66  tff(c_3996, plain, (v1_relat_1(k2_funct_1('#skF_2'))), inference(splitRight, [status(thm)], [c_3984])).
% 7.67/2.66  tff(c_3995, plain, (k5_relat_1(k5_relat_1('#skF_3', '#skF_2'), k2_funct_1('#skF_2'))=k2_funct_1('#skF_2')), inference(splitRight, [status(thm)], [c_3984])).
% 7.67/2.66  tff(c_12, plain, (![A_8, B_12, C_14]: (k5_relat_1(k5_relat_1(A_8, B_12), C_14)=k5_relat_1(A_8, k5_relat_1(B_12, C_14)) | ~v1_relat_1(C_14) | ~v1_relat_1(B_12) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_52])).
% 7.67/2.66  tff(c_4029, plain, (k5_relat_1('#skF_3', k5_relat_1('#skF_2', k2_funct_1('#skF_2')))=k2_funct_1('#skF_2') | ~v1_relat_1(k2_funct_1('#skF_2')) | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3995, c_12])).
% 7.67/2.66  tff(c_4047, plain, (k5_relat_1('#skF_3', k5_relat_1('#skF_2', k2_funct_1('#skF_2')))=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_58, c_3996, c_4029])).
% 7.67/2.66  tff(c_4073, plain, (k5_relat_1('#skF_3', k6_relat_1(k1_relat_1('#skF_2')))=k2_funct_1('#skF_2') | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_42, c_4047])).
% 7.67/2.66  tff(c_4089, plain, (k5_relat_1('#skF_3', k6_relat_1(k1_relat_1('#skF_2')))=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_50, c_4073])).
% 7.67/2.66  tff(c_4108, plain, (![C_14]: (k5_relat_1('#skF_3', k5_relat_1(k6_relat_1(k1_relat_1('#skF_2')), C_14))=k5_relat_1(k2_funct_1('#skF_2'), C_14) | ~v1_relat_1(C_14) | ~v1_relat_1(k6_relat_1(k1_relat_1('#skF_2'))) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_4089, c_12])).
% 7.67/2.66  tff(c_4309, plain, (![C_117]: (k5_relat_1('#skF_3', k5_relat_1(k6_relat_1(k1_relat_1('#skF_2')), C_117))=k5_relat_1(k2_funct_1('#skF_2'), C_117) | ~v1_relat_1(C_117))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_20, c_4108])).
% 7.67/2.66  tff(c_4354, plain, (k5_relat_1(k2_funct_1('#skF_2'), '#skF_2')=k5_relat_1('#skF_3', '#skF_2') | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_14, c_4309])).
% 7.67/2.66  tff(c_4374, plain, (k5_relat_1(k2_funct_1('#skF_2'), '#skF_2')=k5_relat_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_58, c_4354])).
% 7.67/2.66  tff(c_288, plain, (![A_18]: (k1_relat_1(k5_relat_1('#skF_3', k6_relat_1(A_18)))=k1_relat_1('#skF_3') | ~r1_tarski(k1_relat_1('#skF_2'), A_18) | ~v1_relat_1(k6_relat_1(A_18)))), inference(superposition, [status(thm), theory('equality')], [c_64, c_272])).
% 7.67/2.66  tff(c_295, plain, (![A_18]: (k1_relat_1(k5_relat_1('#skF_3', k6_relat_1(A_18)))=k1_relat_1('#skF_3') | ~r1_tarski(k1_relat_1('#skF_2'), A_18))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_288])).
% 7.67/2.66  tff(c_4105, plain, (k1_relat_1(k2_funct_1('#skF_2'))=k1_relat_1('#skF_3') | ~r1_tarski(k1_relat_1('#skF_2'), k1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_4089, c_295])).
% 7.67/2.66  tff(c_4124, plain, (k1_relat_1(k2_funct_1('#skF_2'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_113, c_4105])).
% 7.67/2.66  tff(c_10, plain, (![A_5, B_7]: (k1_relat_1(k5_relat_1(A_5, B_7))=k1_relat_1(A_5) | ~r1_tarski(k2_relat_1(A_5), k1_relat_1(B_7)) | ~v1_relat_1(B_7) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_42])).
% 7.67/2.66  tff(c_335, plain, (![B_7]: (k1_relat_1(k5_relat_1('#skF_2', B_7))=k1_relat_1('#skF_2') | ~r1_tarski(k1_relat_1('#skF_3'), k1_relat_1(B_7)) | ~v1_relat_1(B_7) | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_291, c_10])).
% 7.67/2.66  tff(c_339, plain, (![B_7]: (k1_relat_1(k5_relat_1('#skF_2', B_7))=k1_relat_1('#skF_2') | ~r1_tarski(k1_relat_1('#skF_3'), k1_relat_1(B_7)) | ~v1_relat_1(B_7))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_335])).
% 7.67/2.66  tff(c_4139, plain, (k1_relat_1(k5_relat_1('#skF_2', k2_funct_1('#skF_2')))=k1_relat_1('#skF_2') | ~r1_tarski(k1_relat_1('#skF_3'), k1_relat_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_4124, c_339])).
% 7.67/2.66  tff(c_4172, plain, (k1_relat_1(k5_relat_1('#skF_2', k2_funct_1('#skF_2')))=k1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3996, c_113, c_4139])).
% 7.67/2.66  tff(c_4250, plain, (k5_relat_1(k6_relat_1(k1_relat_1('#skF_2')), k5_relat_1('#skF_2', k2_funct_1('#skF_2')))=k5_relat_1('#skF_2', k2_funct_1('#skF_2')) | ~v1_relat_1(k5_relat_1('#skF_2', k2_funct_1('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_4172, c_14])).
% 7.67/2.66  tff(c_6118, plain, (~v1_relat_1(k5_relat_1('#skF_2', k2_funct_1('#skF_2')))), inference(splitLeft, [status(thm)], [c_4250])).
% 7.67/2.66  tff(c_6121, plain, (~v1_relat_1(k6_relat_1(k1_relat_1('#skF_2'))) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_42, c_6118])).
% 7.67/2.66  tff(c_6124, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_50, c_20, c_6121])).
% 7.67/2.66  tff(c_6125, plain, (k5_relat_1(k6_relat_1(k1_relat_1('#skF_2')), k5_relat_1('#skF_2', k2_funct_1('#skF_2')))=k5_relat_1('#skF_2', k2_funct_1('#skF_2'))), inference(splitRight, [status(thm)], [c_4250])).
% 7.67/2.66  tff(c_6178, plain, (k5_relat_1(k6_relat_1(k1_relat_1('#skF_2')), k6_relat_1(k1_relat_1('#skF_2')))=k5_relat_1('#skF_2', k2_funct_1('#skF_2')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_42, c_6125])).
% 7.67/2.66  tff(c_6208, plain, (k5_relat_1('#skF_2', k2_funct_1('#skF_2'))=k6_relat_1(k1_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_50, c_139, c_6178])).
% 7.67/2.66  tff(c_6249, plain, (![C_14]: (k5_relat_1(k6_relat_1(k1_relat_1('#skF_2')), C_14)=k5_relat_1('#skF_2', k5_relat_1(k2_funct_1('#skF_2'), C_14)) | ~v1_relat_1(C_14) | ~v1_relat_1(k2_funct_1('#skF_2')) | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_6208, c_12])).
% 7.67/2.66  tff(c_6314, plain, (![C_142]: (k5_relat_1(k6_relat_1(k1_relat_1('#skF_2')), C_142)=k5_relat_1('#skF_2', k5_relat_1(k2_funct_1('#skF_2'), C_142)) | ~v1_relat_1(C_142))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_3996, c_6249])).
% 7.67/2.66  tff(c_6392, plain, (k5_relat_1('#skF_2', k5_relat_1(k2_funct_1('#skF_2'), '#skF_2'))='#skF_2' | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_6314, c_14])).
% 7.67/2.66  tff(c_6462, plain, (k5_relat_1('#skF_2', k5_relat_1('#skF_3', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_58, c_4374, c_6392])).
% 7.67/2.66  tff(c_32, plain, (![A_23, B_25]: (v2_funct_1(A_23) | k2_relat_1(B_25)!=k1_relat_1(A_23) | ~v2_funct_1(k5_relat_1(B_25, A_23)) | ~v1_funct_1(B_25) | ~v1_relat_1(B_25) | ~v1_funct_1(A_23) | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_98])).
% 7.67/2.66  tff(c_6567, plain, (v2_funct_1(k5_relat_1('#skF_3', '#skF_2')) | k1_relat_1(k5_relat_1('#skF_3', '#skF_2'))!=k2_relat_1('#skF_2') | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2') | ~v1_funct_1(k5_relat_1('#skF_3', '#skF_2')) | ~v1_relat_1(k5_relat_1('#skF_3', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_6462, c_32])).
% 7.67/2.66  tff(c_6592, plain, (v2_funct_1(k5_relat_1('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_98, c_58, c_56, c_50, c_291, c_330, c_6567])).
% 7.67/2.66  tff(c_6594, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1221, c_6592])).
% 7.67/2.66  tff(c_6596, plain, (v2_funct_1(k5_relat_1('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_1113])).
% 7.67/2.66  tff(c_34, plain, (![B_25, A_23]: (v2_funct_1(B_25) | k2_relat_1(B_25)!=k1_relat_1(A_23) | ~v2_funct_1(k5_relat_1(B_25, A_23)) | ~v1_funct_1(B_25) | ~v1_relat_1(B_25) | ~v1_funct_1(A_23) | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_98])).
% 7.67/2.66  tff(c_6599, plain, (v2_funct_1('#skF_3') | k2_relat_1('#skF_3')!=k1_relat_1('#skF_2') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_6596, c_34])).
% 7.67/2.66  tff(c_6605, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_52, c_48, c_6599])).
% 7.67/2.66  tff(c_6607, plain, $false, inference(negUnitSimplification, [status(thm)], [c_641, c_6605])).
% 7.67/2.66  tff(c_6609, plain, (v2_funct_1('#skF_3')), inference(splitRight, [status(thm)], [c_637])).
% 7.67/2.66  tff(c_40, plain, (![A_27]: (k5_relat_1(k2_funct_1(A_27), A_27)=k6_relat_1(k2_relat_1(A_27)) | ~v2_funct_1(A_27) | ~v1_funct_1(A_27) | ~v1_relat_1(A_27))), inference(cnfTransformation, [status(thm)], [f_118])).
% 7.67/2.66  tff(c_6608, plain, (~v1_relat_1(k2_funct_1('#skF_3')) | k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k5_relat_1('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_637])).
% 7.67/2.66  tff(c_6610, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_6608])).
% 7.67/2.66  tff(c_6613, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_18, c_6610])).
% 7.67/2.66  tff(c_6617, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_6613])).
% 7.67/2.66  tff(c_6619, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_6608])).
% 7.67/2.66  tff(c_6618, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k5_relat_1('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_6608])).
% 7.67/2.66  tff(c_6657, plain, (![C_14]: (k5_relat_1('#skF_3', k5_relat_1(k2_funct_1('#skF_3'), C_14))=k5_relat_1(k5_relat_1('#skF_3', '#skF_2'), C_14) | ~v1_relat_1(C_14) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_6618, c_12])).
% 7.67/2.66  tff(c_6889, plain, (![C_151]: (k5_relat_1('#skF_3', k5_relat_1(k2_funct_1('#skF_3'), C_151))=k5_relat_1(k5_relat_1('#skF_3', '#skF_2'), C_151) | ~v1_relat_1(C_151))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_6619, c_6657])).
% 7.67/2.66  tff(c_6912, plain, (k5_relat_1('#skF_3', k6_relat_1(k2_relat_1('#skF_3')))=k5_relat_1(k5_relat_1('#skF_3', '#skF_2'), '#skF_3') | ~v1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_40, c_6889])).
% 7.67/2.66  tff(c_6922, plain, (k5_relat_1('#skF_3', k6_relat_1(k1_relat_1('#skF_2')))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_6609, c_54, c_48, c_398, c_6912])).
% 7.67/2.66  tff(c_7682, plain, (![A_162]: (k5_relat_1(k6_relat_1(k2_relat_1(A_162)), k2_funct_1(A_162))=k2_funct_1(A_162) | ~v1_relat_1(k2_funct_1(A_162)) | ~v2_funct_1(A_162) | ~v1_funct_1(A_162) | ~v1_relat_1(A_162))), inference(superposition, [status(thm), theory('equality')], [c_185, c_14])).
% 7.67/2.66  tff(c_7710, plain, (k5_relat_1(k6_relat_1(k1_relat_1('#skF_3')), k2_funct_1('#skF_2'))=k2_funct_1('#skF_2') | ~v1_relat_1(k2_funct_1('#skF_2')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_291, c_7682])).
% 7.67/2.66  tff(c_7731, plain, (k5_relat_1(k5_relat_1('#skF_3', '#skF_2'), k2_funct_1('#skF_2'))=k2_funct_1('#skF_2') | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_50, c_331, c_7710])).
% 7.67/2.66  tff(c_7734, plain, (~v1_relat_1(k2_funct_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_7731])).
% 7.67/2.66  tff(c_7737, plain, (~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_18, c_7734])).
% 7.67/2.66  tff(c_7741, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_7737])).
% 7.67/2.66  tff(c_7743, plain, (v1_relat_1(k2_funct_1('#skF_2'))), inference(splitRight, [status(thm)], [c_7731])).
% 7.67/2.66  tff(c_7742, plain, (k5_relat_1(k5_relat_1('#skF_3', '#skF_2'), k2_funct_1('#skF_2'))=k2_funct_1('#skF_2')), inference(splitRight, [status(thm)], [c_7731])).
% 7.67/2.66  tff(c_7762, plain, (k5_relat_1('#skF_3', k5_relat_1('#skF_2', k2_funct_1('#skF_2')))=k2_funct_1('#skF_2') | ~v1_relat_1(k2_funct_1('#skF_2')) | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_7742, c_12])).
% 7.67/2.66  tff(c_7780, plain, (k5_relat_1('#skF_3', k5_relat_1('#skF_2', k2_funct_1('#skF_2')))=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_58, c_7743, c_7762])).
% 7.67/2.66  tff(c_7803, plain, (k5_relat_1('#skF_3', k6_relat_1(k1_relat_1('#skF_2')))=k2_funct_1('#skF_2') | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_42, c_7780])).
% 7.67/2.66  tff(c_7816, plain, (k2_funct_1('#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_50, c_6922, c_7803])).
% 7.67/2.66  tff(c_7818, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_7816])).
% 7.67/2.66  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.67/2.66  
% 7.67/2.66  Inference rules
% 7.67/2.66  ----------------------
% 7.67/2.66  #Ref     : 0
% 7.67/2.66  #Sup     : 1710
% 7.67/2.66  #Fact    : 0
% 7.67/2.66  #Define  : 0
% 7.67/2.66  #Split   : 22
% 7.67/2.66  #Chain   : 0
% 7.67/2.66  #Close   : 0
% 7.67/2.66  
% 7.67/2.66  Ordering : KBO
% 7.67/2.66  
% 7.67/2.66  Simplification rules
% 7.67/2.66  ----------------------
% 7.67/2.66  #Subsume      : 282
% 7.67/2.66  #Demod        : 3134
% 7.67/2.66  #Tautology    : 675
% 7.67/2.66  #SimpNegUnit  : 64
% 7.67/2.66  #BackRed      : 29
% 7.67/2.66  
% 7.67/2.66  #Partial instantiations: 0
% 7.67/2.66  #Strategies tried      : 1
% 7.67/2.66  
% 7.67/2.66  Timing (in seconds)
% 7.67/2.66  ----------------------
% 7.67/2.66  Preprocessing        : 0.34
% 7.67/2.66  Parsing              : 0.18
% 7.67/2.66  CNF conversion       : 0.02
% 7.67/2.66  Main loop            : 1.49
% 7.67/2.66  Inferencing          : 0.46
% 7.67/2.66  Reduction            : 0.60
% 7.67/2.66  Demodulation         : 0.45
% 7.67/2.66  BG Simplification    : 0.06
% 7.67/2.66  Subsumption          : 0.28
% 7.67/2.66  Abstraction          : 0.09
% 7.67/2.66  MUC search           : 0.00
% 7.67/2.66  Cooper               : 0.00
% 7.67/2.66  Total                : 1.88
% 7.67/2.66  Index Insertion      : 0.00
% 7.67/2.66  Index Deletion       : 0.00
% 8.10/2.66  Index Matching       : 0.00
% 8.10/2.66  BG Taut test         : 0.00
%------------------------------------------------------------------------------
