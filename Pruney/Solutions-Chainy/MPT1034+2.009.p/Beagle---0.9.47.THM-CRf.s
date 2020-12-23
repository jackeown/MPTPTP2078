%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:58 EST 2020

% Result     : Theorem 1.93s
% Output     : CNFRefutation 1.93s
% Verified   : 
% Statistics : Number of formulae       :   42 ( 128 expanded)
%              Number of leaves         :   16 (  56 expanded)
%              Depth                    :   10
%              Number of atoms          :  110 ( 598 expanded)
%              Number of equality atoms :    9 (  43 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > r1_partfun1 > m1_subset_1 > v1_funct_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(f_65,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_funct_2)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [D] :
          ( ( v1_funct_1(D)
            & v1_funct_2(D,A,B)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
         => ( r1_partfun1(C,D)
           => ( ( B = k1_xboole_0
                & A != k1_xboole_0 )
              | r2_relset_1(A,B,C,D) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_funct_2)).

tff(c_6,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_20,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_18,plain,(
    v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_8,plain,(
    r1_partfun1('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_16,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_14,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_12,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_10,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_22,plain,(
    ! [B_10,A_11,C_12,D_13] :
      ( k1_xboole_0 = B_10
      | r2_relset_1(A_11,B_10,C_12,D_13)
      | ~ r1_partfun1(C_12,D_13)
      | ~ m1_subset_1(D_13,k1_zfmisc_1(k2_zfmisc_1(A_11,B_10)))
      | ~ v1_funct_2(D_13,A_11,B_10)
      | ~ v1_funct_1(D_13)
      | ~ m1_subset_1(C_12,k1_zfmisc_1(k2_zfmisc_1(A_11,B_10)))
      | ~ v1_funct_2(C_12,A_11,B_10)
      | ~ v1_funct_1(C_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_24,plain,(
    ! [C_12] :
      ( k1_xboole_0 = '#skF_1'
      | r2_relset_1('#skF_1','#skF_1',C_12,'#skF_2')
      | ~ r1_partfun1(C_12,'#skF_2')
      | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
      | ~ v1_funct_1('#skF_2')
      | ~ m1_subset_1(C_12,k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
      | ~ v1_funct_2(C_12,'#skF_1','#skF_1')
      | ~ v1_funct_1(C_12) ) ),
    inference(resolution,[status(thm)],[c_16,c_22])).

tff(c_29,plain,(
    ! [C_12] :
      ( k1_xboole_0 = '#skF_1'
      | r2_relset_1('#skF_1','#skF_1',C_12,'#skF_2')
      | ~ r1_partfun1(C_12,'#skF_2')
      | ~ m1_subset_1(C_12,k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
      | ~ v1_funct_2(C_12,'#skF_1','#skF_1')
      | ~ v1_funct_1(C_12) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_24])).

tff(c_33,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_29])).

tff(c_2,plain,(
    ! [B_2,C_3,D_5] :
      ( r2_relset_1(k1_xboole_0,B_2,C_3,D_5)
      | ~ r1_partfun1(C_3,D_5)
      | ~ m1_subset_1(D_5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_2)))
      | ~ v1_funct_2(D_5,k1_xboole_0,B_2)
      | ~ v1_funct_1(D_5)
      | ~ m1_subset_1(C_3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_2)))
      | ~ v1_funct_2(C_3,k1_xboole_0,B_2)
      | ~ v1_funct_1(C_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_41,plain,(
    ! [B_14,C_15,D_16] :
      ( r2_relset_1('#skF_1',B_14,C_15,D_16)
      | ~ r1_partfun1(C_15,D_16)
      | ~ m1_subset_1(D_16,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_14)))
      | ~ v1_funct_2(D_16,'#skF_1',B_14)
      | ~ v1_funct_1(D_16)
      | ~ m1_subset_1(C_15,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_14)))
      | ~ v1_funct_2(C_15,'#skF_1',B_14)
      | ~ v1_funct_1(C_15) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_33,c_33,c_33,c_33,c_33,c_2])).

tff(c_45,plain,(
    ! [C_15] :
      ( r2_relset_1('#skF_1','#skF_1',C_15,'#skF_3')
      | ~ r1_partfun1(C_15,'#skF_3')
      | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(C_15,k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
      | ~ v1_funct_2(C_15,'#skF_1','#skF_1')
      | ~ v1_funct_1(C_15) ) ),
    inference(resolution,[status(thm)],[c_10,c_41])).

tff(c_79,plain,(
    ! [C_22] :
      ( r2_relset_1('#skF_1','#skF_1',C_22,'#skF_3')
      | ~ r1_partfun1(C_22,'#skF_3')
      | ~ m1_subset_1(C_22,k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
      | ~ v1_funct_2(C_22,'#skF_1','#skF_1')
      | ~ v1_funct_1(C_22) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_12,c_45])).

tff(c_82,plain,
    ( r2_relset_1('#skF_1','#skF_1','#skF_2','#skF_3')
    | ~ r1_partfun1('#skF_2','#skF_3')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_16,c_79])).

tff(c_88,plain,(
    r2_relset_1('#skF_1','#skF_1','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_8,c_82])).

tff(c_90,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6,c_88])).

tff(c_92,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_29])).

tff(c_26,plain,(
    ! [C_12] :
      ( k1_xboole_0 = '#skF_1'
      | r2_relset_1('#skF_1','#skF_1',C_12,'#skF_3')
      | ~ r1_partfun1(C_12,'#skF_3')
      | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(C_12,k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
      | ~ v1_funct_2(C_12,'#skF_1','#skF_1')
      | ~ v1_funct_1(C_12) ) ),
    inference(resolution,[status(thm)],[c_10,c_22])).

tff(c_32,plain,(
    ! [C_12] :
      ( k1_xboole_0 = '#skF_1'
      | r2_relset_1('#skF_1','#skF_1',C_12,'#skF_3')
      | ~ r1_partfun1(C_12,'#skF_3')
      | ~ m1_subset_1(C_12,k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
      | ~ v1_funct_2(C_12,'#skF_1','#skF_1')
      | ~ v1_funct_1(C_12) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_12,c_26])).

tff(c_109,plain,(
    ! [C_24] :
      ( r2_relset_1('#skF_1','#skF_1',C_24,'#skF_3')
      | ~ r1_partfun1(C_24,'#skF_3')
      | ~ m1_subset_1(C_24,k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
      | ~ v1_funct_2(C_24,'#skF_1','#skF_1')
      | ~ v1_funct_1(C_24) ) ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_32])).

tff(c_112,plain,
    ( r2_relset_1('#skF_1','#skF_1','#skF_2','#skF_3')
    | ~ r1_partfun1('#skF_2','#skF_3')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_16,c_109])).

tff(c_118,plain,(
    r2_relset_1('#skF_1','#skF_1','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_8,c_112])).

tff(c_120,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6,c_118])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:34:16 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.93/1.23  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.93/1.23  
% 1.93/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.93/1.23  %$ r2_relset_1 > v1_funct_2 > r1_partfun1 > m1_subset_1 > v1_funct_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.93/1.23  
% 1.93/1.23  %Foreground sorts:
% 1.93/1.23  
% 1.93/1.23  
% 1.93/1.23  %Background operators:
% 1.93/1.23  
% 1.93/1.23  
% 1.93/1.23  %Foreground operators:
% 1.93/1.23  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.93/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.93/1.23  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 1.93/1.23  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.93/1.23  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 1.93/1.23  tff('#skF_2', type, '#skF_2': $i).
% 1.93/1.23  tff('#skF_3', type, '#skF_3': $i).
% 1.93/1.23  tff('#skF_1', type, '#skF_1': $i).
% 1.93/1.23  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.93/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.93/1.23  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.93/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.93/1.23  tff(r1_partfun1, type, r1_partfun1: ($i * $i) > $o).
% 1.93/1.23  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.93/1.24  
% 1.93/1.25  tff(f_65, negated_conjecture, ~(![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, A, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r1_partfun1(B, C) => r2_relset_1(A, A, B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_funct_2)).
% 1.93/1.25  tff(f_47, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_partfun1(C, D) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | r2_relset_1(A, B, C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t142_funct_2)).
% 1.93/1.25  tff(c_6, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.93/1.25  tff(c_20, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.93/1.25  tff(c_18, plain, (v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.93/1.25  tff(c_8, plain, (r1_partfun1('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.93/1.25  tff(c_16, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.93/1.25  tff(c_14, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.93/1.25  tff(c_12, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.93/1.25  tff(c_10, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.93/1.25  tff(c_22, plain, (![B_10, A_11, C_12, D_13]: (k1_xboole_0=B_10 | r2_relset_1(A_11, B_10, C_12, D_13) | ~r1_partfun1(C_12, D_13) | ~m1_subset_1(D_13, k1_zfmisc_1(k2_zfmisc_1(A_11, B_10))) | ~v1_funct_2(D_13, A_11, B_10) | ~v1_funct_1(D_13) | ~m1_subset_1(C_12, k1_zfmisc_1(k2_zfmisc_1(A_11, B_10))) | ~v1_funct_2(C_12, A_11, B_10) | ~v1_funct_1(C_12))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.93/1.25  tff(c_24, plain, (![C_12]: (k1_xboole_0='#skF_1' | r2_relset_1('#skF_1', '#skF_1', C_12, '#skF_2') | ~r1_partfun1(C_12, '#skF_2') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2') | ~m1_subset_1(C_12, k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_2(C_12, '#skF_1', '#skF_1') | ~v1_funct_1(C_12))), inference(resolution, [status(thm)], [c_16, c_22])).
% 1.93/1.25  tff(c_29, plain, (![C_12]: (k1_xboole_0='#skF_1' | r2_relset_1('#skF_1', '#skF_1', C_12, '#skF_2') | ~r1_partfun1(C_12, '#skF_2') | ~m1_subset_1(C_12, k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_2(C_12, '#skF_1', '#skF_1') | ~v1_funct_1(C_12))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_18, c_24])).
% 1.93/1.25  tff(c_33, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_29])).
% 1.93/1.25  tff(c_2, plain, (![B_2, C_3, D_5]: (r2_relset_1(k1_xboole_0, B_2, C_3, D_5) | ~r1_partfun1(C_3, D_5) | ~m1_subset_1(D_5, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_2))) | ~v1_funct_2(D_5, k1_xboole_0, B_2) | ~v1_funct_1(D_5) | ~m1_subset_1(C_3, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_2))) | ~v1_funct_2(C_3, k1_xboole_0, B_2) | ~v1_funct_1(C_3))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.93/1.25  tff(c_41, plain, (![B_14, C_15, D_16]: (r2_relset_1('#skF_1', B_14, C_15, D_16) | ~r1_partfun1(C_15, D_16) | ~m1_subset_1(D_16, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_14))) | ~v1_funct_2(D_16, '#skF_1', B_14) | ~v1_funct_1(D_16) | ~m1_subset_1(C_15, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_14))) | ~v1_funct_2(C_15, '#skF_1', B_14) | ~v1_funct_1(C_15))), inference(demodulation, [status(thm), theory('equality')], [c_33, c_33, c_33, c_33, c_33, c_2])).
% 1.93/1.25  tff(c_45, plain, (![C_15]: (r2_relset_1('#skF_1', '#skF_1', C_15, '#skF_3') | ~r1_partfun1(C_15, '#skF_3') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3') | ~m1_subset_1(C_15, k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_2(C_15, '#skF_1', '#skF_1') | ~v1_funct_1(C_15))), inference(resolution, [status(thm)], [c_10, c_41])).
% 1.93/1.25  tff(c_79, plain, (![C_22]: (r2_relset_1('#skF_1', '#skF_1', C_22, '#skF_3') | ~r1_partfun1(C_22, '#skF_3') | ~m1_subset_1(C_22, k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_2(C_22, '#skF_1', '#skF_1') | ~v1_funct_1(C_22))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_12, c_45])).
% 1.93/1.25  tff(c_82, plain, (r2_relset_1('#skF_1', '#skF_1', '#skF_2', '#skF_3') | ~r1_partfun1('#skF_2', '#skF_3') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_16, c_79])).
% 1.93/1.25  tff(c_88, plain, (r2_relset_1('#skF_1', '#skF_1', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_18, c_8, c_82])).
% 1.93/1.25  tff(c_90, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6, c_88])).
% 1.93/1.25  tff(c_92, plain, (k1_xboole_0!='#skF_1'), inference(splitRight, [status(thm)], [c_29])).
% 1.93/1.25  tff(c_26, plain, (![C_12]: (k1_xboole_0='#skF_1' | r2_relset_1('#skF_1', '#skF_1', C_12, '#skF_3') | ~r1_partfun1(C_12, '#skF_3') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3') | ~m1_subset_1(C_12, k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_2(C_12, '#skF_1', '#skF_1') | ~v1_funct_1(C_12))), inference(resolution, [status(thm)], [c_10, c_22])).
% 1.93/1.25  tff(c_32, plain, (![C_12]: (k1_xboole_0='#skF_1' | r2_relset_1('#skF_1', '#skF_1', C_12, '#skF_3') | ~r1_partfun1(C_12, '#skF_3') | ~m1_subset_1(C_12, k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_2(C_12, '#skF_1', '#skF_1') | ~v1_funct_1(C_12))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_12, c_26])).
% 1.93/1.25  tff(c_109, plain, (![C_24]: (r2_relset_1('#skF_1', '#skF_1', C_24, '#skF_3') | ~r1_partfun1(C_24, '#skF_3') | ~m1_subset_1(C_24, k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_2(C_24, '#skF_1', '#skF_1') | ~v1_funct_1(C_24))), inference(negUnitSimplification, [status(thm)], [c_92, c_32])).
% 1.93/1.25  tff(c_112, plain, (r2_relset_1('#skF_1', '#skF_1', '#skF_2', '#skF_3') | ~r1_partfun1('#skF_2', '#skF_3') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_16, c_109])).
% 1.93/1.25  tff(c_118, plain, (r2_relset_1('#skF_1', '#skF_1', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_18, c_8, c_112])).
% 1.93/1.25  tff(c_120, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6, c_118])).
% 1.93/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.93/1.25  
% 1.93/1.25  Inference rules
% 1.93/1.25  ----------------------
% 1.93/1.25  #Ref     : 0
% 1.93/1.25  #Sup     : 16
% 1.93/1.25  #Fact    : 0
% 1.93/1.25  #Define  : 0
% 1.93/1.25  #Split   : 5
% 1.93/1.25  #Chain   : 0
% 1.93/1.25  #Close   : 0
% 1.93/1.25  
% 1.93/1.25  Ordering : KBO
% 1.93/1.25  
% 1.93/1.25  Simplification rules
% 1.93/1.25  ----------------------
% 1.93/1.25  #Subsume      : 1
% 1.93/1.25  #Demod        : 33
% 1.93/1.25  #Tautology    : 4
% 1.93/1.25  #SimpNegUnit  : 3
% 1.93/1.25  #BackRed      : 2
% 1.93/1.25  
% 1.93/1.25  #Partial instantiations: 0
% 1.93/1.25  #Strategies tried      : 1
% 1.93/1.25  
% 1.93/1.25  Timing (in seconds)
% 1.93/1.25  ----------------------
% 1.93/1.25  Preprocessing        : 0.28
% 1.93/1.25  Parsing              : 0.16
% 1.93/1.25  CNF conversion       : 0.02
% 1.93/1.25  Main loop            : 0.16
% 1.93/1.25  Inferencing          : 0.06
% 1.93/1.25  Reduction            : 0.05
% 1.93/1.25  Demodulation         : 0.04
% 1.93/1.25  BG Simplification    : 0.01
% 1.93/1.25  Subsumption          : 0.03
% 1.93/1.25  Abstraction          : 0.01
% 1.93/1.25  MUC search           : 0.00
% 1.93/1.25  Cooper               : 0.00
% 1.93/1.25  Total                : 0.47
% 1.93/1.25  Index Insertion      : 0.00
% 1.93/1.25  Index Deletion       : 0.00
% 1.93/1.25  Index Matching       : 0.00
% 1.93/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
