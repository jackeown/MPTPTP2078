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
% DateTime   : Thu Dec  3 10:16:57 EST 2020

% Result     : Theorem 1.95s
% Output     : CNFRefutation 1.95s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 186 expanded)
%              Number of leaves         :   19 (  76 expanded)
%              Depth                    :    8
%              Number of atoms          :  115 ( 730 expanded)
%              Number of equality atoms :   15 (  70 expanded)
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

tff(f_85,negated_conjecture,(
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

tff(f_33,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_50,axiom,(
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

tff(f_67,axiom,(
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

tff(c_16,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_27,plain,(
    ! [A_14,B_15,D_16] :
      ( r2_relset_1(A_14,B_15,D_16,D_16)
      | ~ m1_subset_1(D_16,k1_zfmisc_1(k2_zfmisc_1(A_14,B_15))) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_32,plain,(
    r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_16,c_27])).

tff(c_26,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_24,plain,(
    v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_22,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_35,plain,(
    ! [B_19,C_20,A_21] :
      ( k1_xboole_0 = B_19
      | v1_partfun1(C_20,A_21)
      | ~ v1_funct_2(C_20,A_21,B_19)
      | ~ m1_subset_1(C_20,k1_zfmisc_1(k2_zfmisc_1(A_21,B_19)))
      | ~ v1_funct_1(C_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_41,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_partfun1('#skF_2','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_22,c_35])).

tff(c_47,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_partfun1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_41])).

tff(c_62,plain,(
    v1_partfun1('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_47])).

tff(c_20,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_18,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_38,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_partfun1('#skF_3','#skF_1')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_16,c_35])).

tff(c_44,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_partfun1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_38])).

tff(c_48,plain,(
    v1_partfun1('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_14,plain,(
    r1_partfun1('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_63,plain,(
    ! [D_26,C_27,A_28,B_29] :
      ( D_26 = C_27
      | ~ r1_partfun1(C_27,D_26)
      | ~ v1_partfun1(D_26,A_28)
      | ~ v1_partfun1(C_27,A_28)
      | ~ m1_subset_1(D_26,k1_zfmisc_1(k2_zfmisc_1(A_28,B_29)))
      | ~ v1_funct_1(D_26)
      | ~ m1_subset_1(C_27,k1_zfmisc_1(k2_zfmisc_1(A_28,B_29)))
      | ~ v1_funct_1(C_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_65,plain,(
    ! [A_28,B_29] :
      ( '#skF_2' = '#skF_3'
      | ~ v1_partfun1('#skF_3',A_28)
      | ~ v1_partfun1('#skF_2',A_28)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_28,B_29)))
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1(A_28,B_29)))
      | ~ v1_funct_1('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_14,c_63])).

tff(c_68,plain,(
    ! [A_28,B_29] :
      ( '#skF_2' = '#skF_3'
      | ~ v1_partfun1('#skF_3',A_28)
      | ~ v1_partfun1('#skF_2',A_28)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_28,B_29)))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1(A_28,B_29))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_20,c_65])).

tff(c_70,plain,(
    ! [A_30,B_31] :
      ( ~ v1_partfun1('#skF_3',A_30)
      | ~ v1_partfun1('#skF_2',A_30)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_30,B_31)))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1(A_30,B_31))) ) ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_73,plain,
    ( ~ v1_partfun1('#skF_3','#skF_1')
    | ~ v1_partfun1('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_22,c_70])).

tff(c_77,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_62,c_48,c_73])).

tff(c_78,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_12,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_82,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_12])).

tff(c_91,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_82])).

tff(c_93,plain,(
    ~ v1_partfun1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_47])).

tff(c_92,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_47])).

tff(c_6,plain,(
    ! [C_7,B_6] :
      ( v1_partfun1(C_7,k1_xboole_0)
      | ~ v1_funct_2(C_7,k1_xboole_0,B_6)
      | ~ m1_subset_1(C_7,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_6)))
      | ~ v1_funct_1(C_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_100,plain,(
    ! [C_32,B_33] :
      ( v1_partfun1(C_32,'#skF_1')
      | ~ v1_funct_2(C_32,'#skF_1',B_33)
      | ~ m1_subset_1(C_32,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_33)))
      | ~ v1_funct_1(C_32) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_92,c_92,c_6])).

tff(c_106,plain,
    ( v1_partfun1('#skF_2','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_22,c_100])).

tff(c_112,plain,(
    v1_partfun1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_106])).

tff(c_114,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_93,c_112])).

tff(c_116,plain,(
    ~ v1_partfun1('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_115,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_143,plain,(
    ! [C_42,B_43] :
      ( v1_partfun1(C_42,'#skF_1')
      | ~ v1_funct_2(C_42,'#skF_1',B_43)
      | ~ m1_subset_1(C_42,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_43)))
      | ~ v1_funct_1(C_42) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_115,c_115,c_6])).

tff(c_146,plain,
    ( v1_partfun1('#skF_3','#skF_1')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_16,c_143])).

tff(c_152,plain,(
    v1_partfun1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_146])).

tff(c_154,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_116,c_152])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:06:24 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.95/1.30  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.95/1.30  
% 1.95/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.95/1.31  %$ r2_relset_1 > v1_funct_2 > v1_partfun1 > r1_partfun1 > m1_subset_1 > v1_funct_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.95/1.31  
% 1.95/1.31  %Foreground sorts:
% 1.95/1.31  
% 1.95/1.31  
% 1.95/1.31  %Background operators:
% 1.95/1.31  
% 1.95/1.31  
% 1.95/1.31  %Foreground operators:
% 1.95/1.31  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.95/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.95/1.31  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 1.95/1.31  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.95/1.31  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 1.95/1.31  tff('#skF_2', type, '#skF_2': $i).
% 1.95/1.31  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 1.95/1.31  tff('#skF_3', type, '#skF_3': $i).
% 1.95/1.31  tff('#skF_1', type, '#skF_1': $i).
% 1.95/1.31  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.95/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.95/1.31  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.95/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.95/1.31  tff(r1_partfun1, type, r1_partfun1: ($i * $i) > $o).
% 1.95/1.31  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.95/1.31  
% 1.95/1.32  tff(f_85, negated_conjecture, ~(![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, A, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r1_partfun1(B, C) => r2_relset_1(A, A, B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_funct_2)).
% 1.95/1.32  tff(f_33, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 1.95/1.32  tff(f_50, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | v1_partfun1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t132_funct_2)).
% 1.95/1.32  tff(f_67, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: ((v1_funct_1(D) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((v1_partfun1(C, A) & v1_partfun1(D, A)) & r1_partfun1(C, D)) => (C = D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_partfun1)).
% 1.95/1.32  tff(c_16, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_85])).
% 1.95/1.32  tff(c_27, plain, (![A_14, B_15, D_16]: (r2_relset_1(A_14, B_15, D_16, D_16) | ~m1_subset_1(D_16, k1_zfmisc_1(k2_zfmisc_1(A_14, B_15))))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.95/1.32  tff(c_32, plain, (r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_16, c_27])).
% 1.95/1.32  tff(c_26, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_85])).
% 1.95/1.32  tff(c_24, plain, (v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_85])).
% 1.95/1.32  tff(c_22, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_85])).
% 1.95/1.32  tff(c_35, plain, (![B_19, C_20, A_21]: (k1_xboole_0=B_19 | v1_partfun1(C_20, A_21) | ~v1_funct_2(C_20, A_21, B_19) | ~m1_subset_1(C_20, k1_zfmisc_1(k2_zfmisc_1(A_21, B_19))) | ~v1_funct_1(C_20))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.95/1.32  tff(c_41, plain, (k1_xboole_0='#skF_1' | v1_partfun1('#skF_2', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_22, c_35])).
% 1.95/1.32  tff(c_47, plain, (k1_xboole_0='#skF_1' | v1_partfun1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_41])).
% 1.95/1.32  tff(c_62, plain, (v1_partfun1('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_47])).
% 1.95/1.32  tff(c_20, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_85])).
% 1.95/1.32  tff(c_18, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_85])).
% 1.95/1.32  tff(c_38, plain, (k1_xboole_0='#skF_1' | v1_partfun1('#skF_3', '#skF_1') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_16, c_35])).
% 1.95/1.32  tff(c_44, plain, (k1_xboole_0='#skF_1' | v1_partfun1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_18, c_38])).
% 1.95/1.32  tff(c_48, plain, (v1_partfun1('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_44])).
% 1.95/1.32  tff(c_14, plain, (r1_partfun1('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_85])).
% 1.95/1.32  tff(c_63, plain, (![D_26, C_27, A_28, B_29]: (D_26=C_27 | ~r1_partfun1(C_27, D_26) | ~v1_partfun1(D_26, A_28) | ~v1_partfun1(C_27, A_28) | ~m1_subset_1(D_26, k1_zfmisc_1(k2_zfmisc_1(A_28, B_29))) | ~v1_funct_1(D_26) | ~m1_subset_1(C_27, k1_zfmisc_1(k2_zfmisc_1(A_28, B_29))) | ~v1_funct_1(C_27))), inference(cnfTransformation, [status(thm)], [f_67])).
% 1.95/1.32  tff(c_65, plain, (![A_28, B_29]: ('#skF_2'='#skF_3' | ~v1_partfun1('#skF_3', A_28) | ~v1_partfun1('#skF_2', A_28) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_28, B_29))) | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1(A_28, B_29))) | ~v1_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_14, c_63])).
% 1.95/1.32  tff(c_68, plain, (![A_28, B_29]: ('#skF_2'='#skF_3' | ~v1_partfun1('#skF_3', A_28) | ~v1_partfun1('#skF_2', A_28) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_28, B_29))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1(A_28, B_29))))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_20, c_65])).
% 1.95/1.32  tff(c_70, plain, (![A_30, B_31]: (~v1_partfun1('#skF_3', A_30) | ~v1_partfun1('#skF_2', A_30) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_30, B_31))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1(A_30, B_31))))), inference(splitLeft, [status(thm)], [c_68])).
% 1.95/1.32  tff(c_73, plain, (~v1_partfun1('#skF_3', '#skF_1') | ~v1_partfun1('#skF_2', '#skF_1') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_22, c_70])).
% 1.95/1.32  tff(c_77, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_62, c_48, c_73])).
% 1.95/1.32  tff(c_78, plain, ('#skF_2'='#skF_3'), inference(splitRight, [status(thm)], [c_68])).
% 1.95/1.32  tff(c_12, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_85])).
% 1.95/1.32  tff(c_82, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_12])).
% 1.95/1.32  tff(c_91, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_82])).
% 1.95/1.32  tff(c_93, plain, (~v1_partfun1('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_47])).
% 1.95/1.32  tff(c_92, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_47])).
% 1.95/1.32  tff(c_6, plain, (![C_7, B_6]: (v1_partfun1(C_7, k1_xboole_0) | ~v1_funct_2(C_7, k1_xboole_0, B_6) | ~m1_subset_1(C_7, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_6))) | ~v1_funct_1(C_7))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.95/1.32  tff(c_100, plain, (![C_32, B_33]: (v1_partfun1(C_32, '#skF_1') | ~v1_funct_2(C_32, '#skF_1', B_33) | ~m1_subset_1(C_32, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_33))) | ~v1_funct_1(C_32))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_92, c_92, c_6])).
% 1.95/1.32  tff(c_106, plain, (v1_partfun1('#skF_2', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_22, c_100])).
% 1.95/1.32  tff(c_112, plain, (v1_partfun1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_106])).
% 1.95/1.32  tff(c_114, plain, $false, inference(negUnitSimplification, [status(thm)], [c_93, c_112])).
% 1.95/1.32  tff(c_116, plain, (~v1_partfun1('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_44])).
% 1.95/1.32  tff(c_115, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_44])).
% 1.95/1.32  tff(c_143, plain, (![C_42, B_43]: (v1_partfun1(C_42, '#skF_1') | ~v1_funct_2(C_42, '#skF_1', B_43) | ~m1_subset_1(C_42, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_43))) | ~v1_funct_1(C_42))), inference(demodulation, [status(thm), theory('equality')], [c_115, c_115, c_115, c_6])).
% 1.95/1.32  tff(c_146, plain, (v1_partfun1('#skF_3', '#skF_1') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_16, c_143])).
% 1.95/1.32  tff(c_152, plain, (v1_partfun1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_18, c_146])).
% 1.95/1.32  tff(c_154, plain, $false, inference(negUnitSimplification, [status(thm)], [c_116, c_152])).
% 1.95/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.95/1.32  
% 1.95/1.32  Inference rules
% 1.95/1.32  ----------------------
% 1.95/1.32  #Ref     : 0
% 1.95/1.32  #Sup     : 19
% 1.95/1.32  #Fact    : 0
% 1.95/1.32  #Define  : 0
% 1.95/1.32  #Split   : 3
% 1.95/1.32  #Chain   : 0
% 1.95/1.32  #Close   : 0
% 1.95/1.32  
% 1.95/1.32  Ordering : KBO
% 1.95/1.32  
% 1.95/1.32  Simplification rules
% 1.95/1.32  ----------------------
% 1.95/1.32  #Subsume      : 0
% 1.95/1.32  #Demod        : 43
% 1.95/1.32  #Tautology    : 13
% 1.95/1.32  #SimpNegUnit  : 2
% 1.95/1.32  #BackRed      : 11
% 1.95/1.32  
% 1.95/1.32  #Partial instantiations: 0
% 1.95/1.32  #Strategies tried      : 1
% 1.95/1.32  
% 1.95/1.32  Timing (in seconds)
% 1.95/1.32  ----------------------
% 1.95/1.32  Preprocessing        : 0.35
% 1.95/1.32  Parsing              : 0.19
% 1.95/1.32  CNF conversion       : 0.02
% 1.95/1.32  Main loop            : 0.15
% 1.95/1.32  Inferencing          : 0.06
% 1.95/1.32  Reduction            : 0.05
% 1.95/1.32  Demodulation         : 0.03
% 1.95/1.32  BG Simplification    : 0.01
% 1.95/1.32  Subsumption          : 0.02
% 1.95/1.32  Abstraction          : 0.01
% 1.95/1.32  MUC search           : 0.00
% 1.95/1.32  Cooper               : 0.00
% 1.95/1.32  Total                : 0.53
% 1.95/1.32  Index Insertion      : 0.00
% 1.95/1.32  Index Deletion       : 0.00
% 1.95/1.32  Index Matching       : 0.00
% 1.95/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
