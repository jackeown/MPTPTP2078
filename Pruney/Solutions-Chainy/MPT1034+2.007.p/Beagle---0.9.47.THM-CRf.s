%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:58 EST 2020

% Result     : Theorem 1.99s
% Output     : CNFRefutation 2.13s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 189 expanded)
%              Number of leaves         :   19 (  77 expanded)
%              Depth                    :    8
%              Number of atoms          :  117 ( 741 expanded)
%              Number of equality atoms :   14 (  69 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v1_partfun1 > r1_partfun1 > m1_subset_1 > v1_funct_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(r1_partfun1,type,(
    r1_partfun1: ( $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_83,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & v1_funct_2(B,A,A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ! [C] :
            ( ( v1_funct_1(C)
              & v1_funct_2(C,A,A)
              & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
           => ( r1_partfun1(B,C)
             => r2_relset_1(A,A,B,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_funct_2)).

tff(f_31,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( B = k1_xboole_0
            & A != k1_xboole_0 )
          | v1_partfun1(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_funct_2)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [D] :
          ( ( v1_funct_1(D)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
         => ( ( v1_partfun1(C,A)
              & v1_partfun1(D,A)
              & r1_partfun1(C,D) )
           => C = D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_partfun1)).

tff(c_14,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_20,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_41,plain,(
    ! [A_19,B_20,C_21,D_22] :
      ( r2_relset_1(A_19,B_20,C_21,C_21)
      | ~ m1_subset_1(D_22,k1_zfmisc_1(k2_zfmisc_1(A_19,B_20)))
      | ~ m1_subset_1(C_21,k1_zfmisc_1(k2_zfmisc_1(A_19,B_20))) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_54,plain,(
    ! [C_27] :
      ( r2_relset_1('#skF_1','#skF_1',C_27,C_27)
      | ~ m1_subset_1(C_27,k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_20,c_41])).

tff(c_60,plain,(
    r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_14,c_54])).

tff(c_24,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_22,plain,(
    v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_26,plain,(
    ! [B_16,C_17,A_18] :
      ( k1_xboole_0 = B_16
      | v1_partfun1(C_17,A_18)
      | ~ v1_funct_2(C_17,A_18,B_16)
      | ~ m1_subset_1(C_17,k1_zfmisc_1(k2_zfmisc_1(A_18,B_16)))
      | ~ v1_funct_1(C_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_29,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_partfun1('#skF_2','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_20,c_26])).

tff(c_35,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_partfun1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_29])).

tff(c_39,plain,(
    v1_partfun1('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_35])).

tff(c_18,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_16,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_32,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_partfun1('#skF_3','#skF_1')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_14,c_26])).

tff(c_38,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_partfun1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_16,c_32])).

tff(c_40,plain,(
    v1_partfun1('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_12,plain,(
    r1_partfun1('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_48,plain,(
    ! [D_23,C_24,A_25,B_26] :
      ( D_23 = C_24
      | ~ r1_partfun1(C_24,D_23)
      | ~ v1_partfun1(D_23,A_25)
      | ~ v1_partfun1(C_24,A_25)
      | ~ m1_subset_1(D_23,k1_zfmisc_1(k2_zfmisc_1(A_25,B_26)))
      | ~ v1_funct_1(D_23)
      | ~ m1_subset_1(C_24,k1_zfmisc_1(k2_zfmisc_1(A_25,B_26)))
      | ~ v1_funct_1(C_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_50,plain,(
    ! [A_25,B_26] :
      ( '#skF_2' = '#skF_3'
      | ~ v1_partfun1('#skF_3',A_25)
      | ~ v1_partfun1('#skF_2',A_25)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_25,B_26)))
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1(A_25,B_26)))
      | ~ v1_funct_1('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_12,c_48])).

tff(c_53,plain,(
    ! [A_25,B_26] :
      ( '#skF_2' = '#skF_3'
      | ~ v1_partfun1('#skF_3',A_25)
      | ~ v1_partfun1('#skF_2',A_25)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_25,B_26)))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1(A_25,B_26))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_18,c_50])).

tff(c_62,plain,(
    ! [A_28,B_29] :
      ( ~ v1_partfun1('#skF_3',A_28)
      | ~ v1_partfun1('#skF_2',A_28)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_28,B_29)))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1(A_28,B_29))) ) ),
    inference(splitLeft,[status(thm)],[c_53])).

tff(c_65,plain,
    ( ~ v1_partfun1('#skF_3','#skF_1')
    | ~ v1_partfun1('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_20,c_62])).

tff(c_69,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_39,c_40,c_65])).

tff(c_70,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_53])).

tff(c_10,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_74,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_10])).

tff(c_83,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_74])).

tff(c_85,plain,(
    ~ v1_partfun1('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_84,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_4,plain,(
    ! [C_7,B_6] :
      ( v1_partfun1(C_7,k1_xboole_0)
      | ~ v1_funct_2(C_7,k1_xboole_0,B_6)
      | ~ m1_subset_1(C_7,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_6)))
      | ~ v1_funct_1(C_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_106,plain,(
    ! [C_35,B_36] :
      ( v1_partfun1(C_35,'#skF_1')
      | ~ v1_funct_2(C_35,'#skF_1',B_36)
      | ~ m1_subset_1(C_35,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_36)))
      | ~ v1_funct_1(C_35) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_84,c_84,c_4])).

tff(c_112,plain,
    ( v1_partfun1('#skF_3','#skF_1')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_14,c_106])).

tff(c_118,plain,(
    v1_partfun1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_16,c_112])).

tff(c_120,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_85,c_118])).

tff(c_122,plain,(
    ~ v1_partfun1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_35])).

tff(c_121,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_35])).

tff(c_130,plain,(
    ! [C_37,B_38] :
      ( v1_partfun1(C_37,'#skF_1')
      | ~ v1_funct_2(C_37,'#skF_1',B_38)
      | ~ m1_subset_1(C_37,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_38)))
      | ~ v1_funct_1(C_37) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_121,c_121,c_4])).

tff(c_133,plain,
    ( v1_partfun1('#skF_2','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_20,c_130])).

tff(c_139,plain,(
    v1_partfun1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_133])).

tff(c_141,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_122,c_139])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n018.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:35:57 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.99/1.22  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.99/1.23  
% 1.99/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.99/1.23  %$ r2_relset_1 > v1_funct_2 > v1_partfun1 > r1_partfun1 > m1_subset_1 > v1_funct_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.99/1.23  
% 1.99/1.23  %Foreground sorts:
% 1.99/1.23  
% 1.99/1.23  
% 1.99/1.23  %Background operators:
% 1.99/1.23  
% 1.99/1.23  
% 1.99/1.23  %Foreground operators:
% 1.99/1.23  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.99/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.99/1.23  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 1.99/1.23  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.99/1.23  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 1.99/1.23  tff('#skF_2', type, '#skF_2': $i).
% 1.99/1.23  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 1.99/1.23  tff('#skF_3', type, '#skF_3': $i).
% 1.99/1.23  tff('#skF_1', type, '#skF_1': $i).
% 1.99/1.23  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.99/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.99/1.23  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.99/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.99/1.23  tff(r1_partfun1, type, r1_partfun1: ($i * $i) > $o).
% 1.99/1.23  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.99/1.23  
% 2.13/1.25  tff(f_83, negated_conjecture, ~(![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, A, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r1_partfun1(B, C) => r2_relset_1(A, A, B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_funct_2)).
% 2.13/1.25  tff(f_31, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 2.13/1.25  tff(f_48, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | v1_partfun1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t132_funct_2)).
% 2.13/1.25  tff(f_65, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: ((v1_funct_1(D) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((v1_partfun1(C, A) & v1_partfun1(D, A)) & r1_partfun1(C, D)) => (C = D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_partfun1)).
% 2.13/1.25  tff(c_14, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.13/1.25  tff(c_20, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.13/1.25  tff(c_41, plain, (![A_19, B_20, C_21, D_22]: (r2_relset_1(A_19, B_20, C_21, C_21) | ~m1_subset_1(D_22, k1_zfmisc_1(k2_zfmisc_1(A_19, B_20))) | ~m1_subset_1(C_21, k1_zfmisc_1(k2_zfmisc_1(A_19, B_20))))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.13/1.25  tff(c_54, plain, (![C_27]: (r2_relset_1('#skF_1', '#skF_1', C_27, C_27) | ~m1_subset_1(C_27, k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))))), inference(resolution, [status(thm)], [c_20, c_41])).
% 2.13/1.25  tff(c_60, plain, (r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_14, c_54])).
% 2.13/1.25  tff(c_24, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.13/1.25  tff(c_22, plain, (v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.13/1.25  tff(c_26, plain, (![B_16, C_17, A_18]: (k1_xboole_0=B_16 | v1_partfun1(C_17, A_18) | ~v1_funct_2(C_17, A_18, B_16) | ~m1_subset_1(C_17, k1_zfmisc_1(k2_zfmisc_1(A_18, B_16))) | ~v1_funct_1(C_17))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.13/1.25  tff(c_29, plain, (k1_xboole_0='#skF_1' | v1_partfun1('#skF_2', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_20, c_26])).
% 2.13/1.25  tff(c_35, plain, (k1_xboole_0='#skF_1' | v1_partfun1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_29])).
% 2.13/1.25  tff(c_39, plain, (v1_partfun1('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_35])).
% 2.13/1.25  tff(c_18, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.13/1.25  tff(c_16, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.13/1.25  tff(c_32, plain, (k1_xboole_0='#skF_1' | v1_partfun1('#skF_3', '#skF_1') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_14, c_26])).
% 2.13/1.25  tff(c_38, plain, (k1_xboole_0='#skF_1' | v1_partfun1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_16, c_32])).
% 2.13/1.25  tff(c_40, plain, (v1_partfun1('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_38])).
% 2.13/1.25  tff(c_12, plain, (r1_partfun1('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.13/1.25  tff(c_48, plain, (![D_23, C_24, A_25, B_26]: (D_23=C_24 | ~r1_partfun1(C_24, D_23) | ~v1_partfun1(D_23, A_25) | ~v1_partfun1(C_24, A_25) | ~m1_subset_1(D_23, k1_zfmisc_1(k2_zfmisc_1(A_25, B_26))) | ~v1_funct_1(D_23) | ~m1_subset_1(C_24, k1_zfmisc_1(k2_zfmisc_1(A_25, B_26))) | ~v1_funct_1(C_24))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.13/1.25  tff(c_50, plain, (![A_25, B_26]: ('#skF_2'='#skF_3' | ~v1_partfun1('#skF_3', A_25) | ~v1_partfun1('#skF_2', A_25) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_25, B_26))) | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1(A_25, B_26))) | ~v1_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_12, c_48])).
% 2.13/1.25  tff(c_53, plain, (![A_25, B_26]: ('#skF_2'='#skF_3' | ~v1_partfun1('#skF_3', A_25) | ~v1_partfun1('#skF_2', A_25) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_25, B_26))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1(A_25, B_26))))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_18, c_50])).
% 2.13/1.25  tff(c_62, plain, (![A_28, B_29]: (~v1_partfun1('#skF_3', A_28) | ~v1_partfun1('#skF_2', A_28) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_28, B_29))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1(A_28, B_29))))), inference(splitLeft, [status(thm)], [c_53])).
% 2.13/1.25  tff(c_65, plain, (~v1_partfun1('#skF_3', '#skF_1') | ~v1_partfun1('#skF_2', '#skF_1') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_20, c_62])).
% 2.13/1.25  tff(c_69, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_39, c_40, c_65])).
% 2.13/1.25  tff(c_70, plain, ('#skF_2'='#skF_3'), inference(splitRight, [status(thm)], [c_53])).
% 2.13/1.25  tff(c_10, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.13/1.25  tff(c_74, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_10])).
% 2.13/1.25  tff(c_83, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_74])).
% 2.13/1.25  tff(c_85, plain, (~v1_partfun1('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_38])).
% 2.13/1.25  tff(c_84, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_38])).
% 2.13/1.25  tff(c_4, plain, (![C_7, B_6]: (v1_partfun1(C_7, k1_xboole_0) | ~v1_funct_2(C_7, k1_xboole_0, B_6) | ~m1_subset_1(C_7, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_6))) | ~v1_funct_1(C_7))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.13/1.25  tff(c_106, plain, (![C_35, B_36]: (v1_partfun1(C_35, '#skF_1') | ~v1_funct_2(C_35, '#skF_1', B_36) | ~m1_subset_1(C_35, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_36))) | ~v1_funct_1(C_35))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_84, c_84, c_4])).
% 2.13/1.25  tff(c_112, plain, (v1_partfun1('#skF_3', '#skF_1') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_14, c_106])).
% 2.13/1.25  tff(c_118, plain, (v1_partfun1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_16, c_112])).
% 2.13/1.25  tff(c_120, plain, $false, inference(negUnitSimplification, [status(thm)], [c_85, c_118])).
% 2.13/1.25  tff(c_122, plain, (~v1_partfun1('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_35])).
% 2.13/1.25  tff(c_121, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_35])).
% 2.13/1.25  tff(c_130, plain, (![C_37, B_38]: (v1_partfun1(C_37, '#skF_1') | ~v1_funct_2(C_37, '#skF_1', B_38) | ~m1_subset_1(C_37, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_38))) | ~v1_funct_1(C_37))), inference(demodulation, [status(thm), theory('equality')], [c_121, c_121, c_121, c_4])).
% 2.13/1.25  tff(c_133, plain, (v1_partfun1('#skF_2', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_20, c_130])).
% 2.13/1.25  tff(c_139, plain, (v1_partfun1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_133])).
% 2.13/1.25  tff(c_141, plain, $false, inference(negUnitSimplification, [status(thm)], [c_122, c_139])).
% 2.13/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.13/1.25  
% 2.13/1.25  Inference rules
% 2.13/1.25  ----------------------
% 2.13/1.25  #Ref     : 0
% 2.13/1.25  #Sup     : 20
% 2.13/1.25  #Fact    : 0
% 2.13/1.25  #Define  : 0
% 2.13/1.25  #Split   : 3
% 2.13/1.25  #Chain   : 0
% 2.13/1.25  #Close   : 0
% 2.13/1.25  
% 2.13/1.25  Ordering : KBO
% 2.13/1.25  
% 2.13/1.25  Simplification rules
% 2.13/1.25  ----------------------
% 2.13/1.25  #Subsume      : 2
% 2.13/1.25  #Demod        : 37
% 2.13/1.25  #Tautology    : 9
% 2.13/1.25  #SimpNegUnit  : 2
% 2.13/1.25  #BackRed      : 11
% 2.13/1.25  
% 2.13/1.25  #Partial instantiations: 0
% 2.13/1.25  #Strategies tried      : 1
% 2.13/1.25  
% 2.13/1.25  Timing (in seconds)
% 2.13/1.25  ----------------------
% 2.13/1.25  Preprocessing        : 0.30
% 2.13/1.25  Parsing              : 0.17
% 2.13/1.25  CNF conversion       : 0.02
% 2.13/1.25  Main loop            : 0.17
% 2.13/1.25  Inferencing          : 0.07
% 2.13/1.25  Reduction            : 0.05
% 2.13/1.25  Demodulation         : 0.04
% 2.13/1.25  BG Simplification    : 0.01
% 2.13/1.25  Subsumption          : 0.02
% 2.13/1.25  Abstraction          : 0.01
% 2.13/1.25  MUC search           : 0.00
% 2.13/1.25  Cooper               : 0.00
% 2.13/1.25  Total                : 0.51
% 2.13/1.25  Index Insertion      : 0.00
% 2.13/1.25  Index Deletion       : 0.00
% 2.13/1.25  Index Matching       : 0.00
% 2.13/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
