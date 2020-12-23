%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:03 EST 2020

% Result     : Theorem 1.74s
% Output     : CNFRefutation 1.74s
% Verified   : 
% Statistics : Number of formulae       :   39 ( 103 expanded)
%              Number of leaves         :   17 (  47 expanded)
%              Depth                    :   10
%              Number of atoms          :   82 ( 404 expanded)
%              Number of equality atoms :    6 (  31 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_partfun1 > m1_subset_1 > v1_funct_1 > k5_partfun1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff(k5_partfun1,type,(
    k5_partfun1: ( $i * $i * $i ) > $i )).

tff(r1_partfun1,type,(
    r1_partfun1: ( $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_61,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ! [C] :
            ( ( v1_funct_1(C)
              & v1_funct_2(C,A,A)
              & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
           => ( r1_partfun1(B,C)
             => r2_hidden(C,k5_partfun1(A,A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t156_funct_2)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [D] :
          ( ( v1_funct_1(D)
            & v1_funct_2(D,A,B)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
         => ( r1_partfun1(C,D)
           => ( ( B = k1_xboole_0
                & A != k1_xboole_0 )
              | r2_hidden(D,k5_partfun1(A,B,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t155_funct_2)).

tff(c_6,plain,(
    ~ r2_hidden('#skF_3',k5_partfun1('#skF_1','#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_18,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_8,plain,(
    r1_partfun1('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_16,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_14,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_12,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_10,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_20,plain,(
    ! [B_10,D_11,A_12,C_13] :
      ( k1_xboole_0 = B_10
      | r2_hidden(D_11,k5_partfun1(A_12,B_10,C_13))
      | ~ r1_partfun1(C_13,D_11)
      | ~ m1_subset_1(D_11,k1_zfmisc_1(k2_zfmisc_1(A_12,B_10)))
      | ~ v1_funct_2(D_11,A_12,B_10)
      | ~ v1_funct_1(D_11)
      | ~ m1_subset_1(C_13,k1_zfmisc_1(k2_zfmisc_1(A_12,B_10)))
      | ~ v1_funct_1(C_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_22,plain,(
    ! [C_13] :
      ( k1_xboole_0 = '#skF_1'
      | r2_hidden('#skF_3',k5_partfun1('#skF_1','#skF_1',C_13))
      | ~ r1_partfun1(C_13,'#skF_3')
      | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(C_13,k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
      | ~ v1_funct_1(C_13) ) ),
    inference(resolution,[status(thm)],[c_10,c_20])).

tff(c_27,plain,(
    ! [C_13] :
      ( k1_xboole_0 = '#skF_1'
      | r2_hidden('#skF_3',k5_partfun1('#skF_1','#skF_1',C_13))
      | ~ r1_partfun1(C_13,'#skF_3')
      | ~ m1_subset_1(C_13,k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
      | ~ v1_funct_1(C_13) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_12,c_22])).

tff(c_31,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_27])).

tff(c_2,plain,(
    ! [D_5,B_2,C_3] :
      ( r2_hidden(D_5,k5_partfun1(k1_xboole_0,B_2,C_3))
      | ~ r1_partfun1(C_3,D_5)
      | ~ m1_subset_1(D_5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_2)))
      | ~ v1_funct_2(D_5,k1_xboole_0,B_2)
      | ~ v1_funct_1(D_5)
      | ~ m1_subset_1(C_3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_2)))
      | ~ v1_funct_1(C_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_39,plain,(
    ! [D_14,B_15,C_16] :
      ( r2_hidden(D_14,k5_partfun1('#skF_1',B_15,C_16))
      | ~ r1_partfun1(C_16,D_14)
      | ~ m1_subset_1(D_14,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_15)))
      | ~ v1_funct_2(D_14,'#skF_1',B_15)
      | ~ v1_funct_1(D_14)
      | ~ m1_subset_1(C_16,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_15)))
      | ~ v1_funct_1(C_16) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_31,c_31,c_31,c_31,c_2])).

tff(c_41,plain,(
    ! [C_16] :
      ( r2_hidden('#skF_3',k5_partfun1('#skF_1','#skF_1',C_16))
      | ~ r1_partfun1(C_16,'#skF_3')
      | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(C_16,k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
      | ~ v1_funct_1(C_16) ) ),
    inference(resolution,[status(thm)],[c_10,c_39])).

tff(c_50,plain,(
    ! [C_17] :
      ( r2_hidden('#skF_3',k5_partfun1('#skF_1','#skF_1',C_17))
      | ~ r1_partfun1(C_17,'#skF_3')
      | ~ m1_subset_1(C_17,k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
      | ~ v1_funct_1(C_17) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_12,c_41])).

tff(c_56,plain,
    ( r2_hidden('#skF_3',k5_partfun1('#skF_1','#skF_1','#skF_2'))
    | ~ r1_partfun1('#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_16,c_50])).

tff(c_62,plain,(
    r2_hidden('#skF_3',k5_partfun1('#skF_1','#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_8,c_56])).

tff(c_64,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6,c_62])).

tff(c_67,plain,(
    ! [C_18] :
      ( r2_hidden('#skF_3',k5_partfun1('#skF_1','#skF_1',C_18))
      | ~ r1_partfun1(C_18,'#skF_3')
      | ~ m1_subset_1(C_18,k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
      | ~ v1_funct_1(C_18) ) ),
    inference(splitRight,[status(thm)],[c_27])).

tff(c_73,plain,
    ( r2_hidden('#skF_3',k5_partfun1('#skF_1','#skF_1','#skF_2'))
    | ~ r1_partfun1('#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_16,c_67])).

tff(c_79,plain,(
    r2_hidden('#skF_3',k5_partfun1('#skF_1','#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_8,c_73])).

tff(c_81,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6,c_79])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:12:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.74/1.14  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.74/1.15  
% 1.74/1.15  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.74/1.15  %$ v1_funct_2 > r2_hidden > r1_partfun1 > m1_subset_1 > v1_funct_1 > k5_partfun1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.74/1.15  
% 1.74/1.15  %Foreground sorts:
% 1.74/1.15  
% 1.74/1.15  
% 1.74/1.15  %Background operators:
% 1.74/1.15  
% 1.74/1.15  
% 1.74/1.15  %Foreground operators:
% 1.74/1.15  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.74/1.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.74/1.15  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.74/1.15  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.74/1.15  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 1.74/1.15  tff('#skF_2', type, '#skF_2': $i).
% 1.74/1.15  tff('#skF_3', type, '#skF_3': $i).
% 1.74/1.15  tff('#skF_1', type, '#skF_1': $i).
% 1.74/1.15  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.74/1.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.74/1.15  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.74/1.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.74/1.15  tff(k5_partfun1, type, k5_partfun1: ($i * $i * $i) > $i).
% 1.74/1.15  tff(r1_partfun1, type, r1_partfun1: ($i * $i) > $o).
% 1.74/1.15  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.74/1.15  
% 1.74/1.16  tff(f_61, negated_conjecture, ~(![A, B]: ((v1_funct_1(B) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, A, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r1_partfun1(B, C) => r2_hidden(C, k5_partfun1(A, A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t156_funct_2)).
% 1.74/1.16  tff(f_45, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_partfun1(C, D) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | r2_hidden(D, k5_partfun1(A, B, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t155_funct_2)).
% 1.74/1.16  tff(c_6, plain, (~r2_hidden('#skF_3', k5_partfun1('#skF_1', '#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.74/1.16  tff(c_18, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.74/1.16  tff(c_8, plain, (r1_partfun1('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.74/1.16  tff(c_16, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.74/1.16  tff(c_14, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.74/1.16  tff(c_12, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.74/1.16  tff(c_10, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.74/1.16  tff(c_20, plain, (![B_10, D_11, A_12, C_13]: (k1_xboole_0=B_10 | r2_hidden(D_11, k5_partfun1(A_12, B_10, C_13)) | ~r1_partfun1(C_13, D_11) | ~m1_subset_1(D_11, k1_zfmisc_1(k2_zfmisc_1(A_12, B_10))) | ~v1_funct_2(D_11, A_12, B_10) | ~v1_funct_1(D_11) | ~m1_subset_1(C_13, k1_zfmisc_1(k2_zfmisc_1(A_12, B_10))) | ~v1_funct_1(C_13))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.74/1.16  tff(c_22, plain, (![C_13]: (k1_xboole_0='#skF_1' | r2_hidden('#skF_3', k5_partfun1('#skF_1', '#skF_1', C_13)) | ~r1_partfun1(C_13, '#skF_3') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3') | ~m1_subset_1(C_13, k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_1(C_13))), inference(resolution, [status(thm)], [c_10, c_20])).
% 1.74/1.16  tff(c_27, plain, (![C_13]: (k1_xboole_0='#skF_1' | r2_hidden('#skF_3', k5_partfun1('#skF_1', '#skF_1', C_13)) | ~r1_partfun1(C_13, '#skF_3') | ~m1_subset_1(C_13, k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_1(C_13))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_12, c_22])).
% 1.74/1.16  tff(c_31, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_27])).
% 1.74/1.16  tff(c_2, plain, (![D_5, B_2, C_3]: (r2_hidden(D_5, k5_partfun1(k1_xboole_0, B_2, C_3)) | ~r1_partfun1(C_3, D_5) | ~m1_subset_1(D_5, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_2))) | ~v1_funct_2(D_5, k1_xboole_0, B_2) | ~v1_funct_1(D_5) | ~m1_subset_1(C_3, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_2))) | ~v1_funct_1(C_3))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.74/1.16  tff(c_39, plain, (![D_14, B_15, C_16]: (r2_hidden(D_14, k5_partfun1('#skF_1', B_15, C_16)) | ~r1_partfun1(C_16, D_14) | ~m1_subset_1(D_14, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_15))) | ~v1_funct_2(D_14, '#skF_1', B_15) | ~v1_funct_1(D_14) | ~m1_subset_1(C_16, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_15))) | ~v1_funct_1(C_16))), inference(demodulation, [status(thm), theory('equality')], [c_31, c_31, c_31, c_31, c_2])).
% 1.74/1.16  tff(c_41, plain, (![C_16]: (r2_hidden('#skF_3', k5_partfun1('#skF_1', '#skF_1', C_16)) | ~r1_partfun1(C_16, '#skF_3') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3') | ~m1_subset_1(C_16, k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_1(C_16))), inference(resolution, [status(thm)], [c_10, c_39])).
% 1.74/1.16  tff(c_50, plain, (![C_17]: (r2_hidden('#skF_3', k5_partfun1('#skF_1', '#skF_1', C_17)) | ~r1_partfun1(C_17, '#skF_3') | ~m1_subset_1(C_17, k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_1(C_17))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_12, c_41])).
% 1.74/1.16  tff(c_56, plain, (r2_hidden('#skF_3', k5_partfun1('#skF_1', '#skF_1', '#skF_2')) | ~r1_partfun1('#skF_2', '#skF_3') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_16, c_50])).
% 1.74/1.16  tff(c_62, plain, (r2_hidden('#skF_3', k5_partfun1('#skF_1', '#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_8, c_56])).
% 1.74/1.16  tff(c_64, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6, c_62])).
% 1.74/1.16  tff(c_67, plain, (![C_18]: (r2_hidden('#skF_3', k5_partfun1('#skF_1', '#skF_1', C_18)) | ~r1_partfun1(C_18, '#skF_3') | ~m1_subset_1(C_18, k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_1(C_18))), inference(splitRight, [status(thm)], [c_27])).
% 1.74/1.16  tff(c_73, plain, (r2_hidden('#skF_3', k5_partfun1('#skF_1', '#skF_1', '#skF_2')) | ~r1_partfun1('#skF_2', '#skF_3') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_16, c_67])).
% 1.74/1.16  tff(c_79, plain, (r2_hidden('#skF_3', k5_partfun1('#skF_1', '#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_8, c_73])).
% 1.74/1.16  tff(c_81, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6, c_79])).
% 1.74/1.16  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.74/1.16  
% 1.74/1.16  Inference rules
% 1.74/1.16  ----------------------
% 1.74/1.16  #Ref     : 0
% 1.74/1.16  #Sup     : 10
% 1.74/1.16  #Fact    : 0
% 1.74/1.16  #Define  : 0
% 1.74/1.16  #Split   : 1
% 1.74/1.16  #Chain   : 0
% 1.74/1.16  #Close   : 0
% 1.74/1.16  
% 1.74/1.16  Ordering : KBO
% 1.74/1.16  
% 1.74/1.16  Simplification rules
% 1.74/1.16  ----------------------
% 1.74/1.16  #Subsume      : 0
% 1.74/1.16  #Demod        : 18
% 1.74/1.16  #Tautology    : 3
% 1.74/1.16  #SimpNegUnit  : 2
% 1.74/1.16  #BackRed      : 2
% 1.74/1.16  
% 1.74/1.16  #Partial instantiations: 0
% 1.74/1.16  #Strategies tried      : 1
% 1.74/1.16  
% 1.74/1.16  Timing (in seconds)
% 1.74/1.16  ----------------------
% 1.74/1.16  Preprocessing        : 0.27
% 1.74/1.16  Parsing              : 0.16
% 1.74/1.16  CNF conversion       : 0.02
% 1.74/1.16  Main loop            : 0.13
% 1.74/1.16  Inferencing          : 0.05
% 1.74/1.16  Reduction            : 0.04
% 1.74/1.16  Demodulation         : 0.03
% 1.74/1.16  BG Simplification    : 0.01
% 1.74/1.16  Subsumption          : 0.02
% 1.74/1.16  Abstraction          : 0.01
% 1.74/1.16  MUC search           : 0.00
% 1.74/1.16  Cooper               : 0.00
% 1.74/1.16  Total                : 0.43
% 1.74/1.16  Index Insertion      : 0.00
% 1.74/1.17  Index Deletion       : 0.00
% 1.74/1.17  Index Matching       : 0.00
% 1.74/1.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
