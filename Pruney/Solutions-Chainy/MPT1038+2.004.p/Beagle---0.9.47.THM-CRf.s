%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:01 EST 2020

% Result     : Theorem 1.74s
% Output     : CNFRefutation 1.99s
% Verified   : 
% Statistics : Number of formulae       :   47 ( 109 expanded)
%              Number of leaves         :   18 (  49 expanded)
%              Depth                    :    8
%              Number of atoms          :  106 ( 469 expanded)
%              Number of equality atoms :    6 (  30 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v1_partfun1 > r1_partfun1 > m1_subset_1 > v1_funct_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(r1_partfun1,type,(
    r1_partfun1: ( $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_87,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ! [C] :
            ( ( v1_funct_1(C)
              & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
           => ! [D] :
                ( ( v1_funct_1(D)
                  & v1_funct_2(D,A,A)
                  & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
               => ( ( r1_partfun1(B,D)
                    & r1_partfun1(C,D) )
                 => r1_partfun1(B,C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_funct_2)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( B = k1_xboole_0
            & A != k1_xboole_0 )
          | v1_partfun1(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_funct_2)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [D] :
          ( ( v1_funct_1(D)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
         => ! [E] :
              ( ( v1_funct_1(E)
                & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
             => ( ( r1_partfun1(C,E)
                  & r1_partfun1(D,E)
                  & v1_partfun1(E,A) )
               => r1_partfun1(C,D) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t158_partfun1)).

tff(c_8,plain,(
    ~ r1_partfun1('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_26,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_12,plain,(
    r1_partfun1('#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_24,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_14,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_18,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_16,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_28,plain,(
    ! [B_19,C_20,A_21] :
      ( k1_xboole_0 = B_19
      | v1_partfun1(C_20,A_21)
      | ~ v1_funct_2(C_20,A_21,B_19)
      | ~ m1_subset_1(C_20,k1_zfmisc_1(k2_zfmisc_1(A_21,B_19)))
      | ~ v1_funct_1(C_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_31,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_partfun1('#skF_4','#skF_1')
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_14,c_28])).

tff(c_40,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_partfun1('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_16,c_31])).

tff(c_47,plain,(
    v1_partfun1('#skF_4','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_20,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_22,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_10,plain,(
    r1_partfun1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_49,plain,(
    ! [E_25,A_26,D_22,B_23,C_24] :
      ( r1_partfun1(C_24,D_22)
      | ~ v1_partfun1(E_25,A_26)
      | ~ r1_partfun1(D_22,E_25)
      | ~ r1_partfun1(C_24,E_25)
      | ~ m1_subset_1(E_25,k1_zfmisc_1(k2_zfmisc_1(A_26,B_23)))
      | ~ v1_funct_1(E_25)
      | ~ m1_subset_1(D_22,k1_zfmisc_1(k2_zfmisc_1(A_26,B_23)))
      | ~ v1_funct_1(D_22)
      | ~ m1_subset_1(C_24,k1_zfmisc_1(k2_zfmisc_1(A_26,B_23)))
      | ~ v1_funct_1(C_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_51,plain,(
    ! [C_24,A_26,B_23] :
      ( r1_partfun1(C_24,'#skF_3')
      | ~ v1_partfun1('#skF_4',A_26)
      | ~ r1_partfun1(C_24,'#skF_4')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_26,B_23)))
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_26,B_23)))
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(C_24,k1_zfmisc_1(k2_zfmisc_1(A_26,B_23)))
      | ~ v1_funct_1(C_24) ) ),
    inference(resolution,[status(thm)],[c_10,c_49])).

tff(c_61,plain,(
    ! [C_27,A_28,B_29] :
      ( r1_partfun1(C_27,'#skF_3')
      | ~ v1_partfun1('#skF_4',A_28)
      | ~ r1_partfun1(C_27,'#skF_4')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_28,B_29)))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_28,B_29)))
      | ~ m1_subset_1(C_27,k1_zfmisc_1(k2_zfmisc_1(A_28,B_29)))
      | ~ v1_funct_1(C_27) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_18,c_51])).

tff(c_63,plain,(
    ! [C_27] :
      ( r1_partfun1(C_27,'#skF_3')
      | ~ v1_partfun1('#skF_4','#skF_1')
      | ~ r1_partfun1(C_27,'#skF_4')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
      | ~ m1_subset_1(C_27,k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
      | ~ v1_funct_1(C_27) ) ),
    inference(resolution,[status(thm)],[c_20,c_61])).

tff(c_67,plain,(
    ! [C_30] :
      ( r1_partfun1(C_30,'#skF_3')
      | ~ r1_partfun1(C_30,'#skF_4')
      | ~ m1_subset_1(C_30,k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
      | ~ v1_funct_1(C_30) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_47,c_63])).

tff(c_73,plain,
    ( r1_partfun1('#skF_2','#skF_3')
    | ~ r1_partfun1('#skF_2','#skF_4')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_67])).

tff(c_82,plain,(
    r1_partfun1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_12,c_73])).

tff(c_84,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8,c_82])).

tff(c_86,plain,(
    ~ v1_partfun1('#skF_4','#skF_1') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_85,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_2,plain,(
    ! [C_3,B_2] :
      ( v1_partfun1(C_3,k1_xboole_0)
      | ~ v1_funct_2(C_3,k1_xboole_0,B_2)
      | ~ m1_subset_1(C_3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_2)))
      | ~ v1_funct_1(C_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_106,plain,(
    ! [C_36,B_37] :
      ( v1_partfun1(C_36,'#skF_1')
      | ~ v1_funct_2(C_36,'#skF_1',B_37)
      | ~ m1_subset_1(C_36,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_37)))
      | ~ v1_funct_1(C_36) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_85,c_85,c_2])).

tff(c_109,plain,
    ( v1_partfun1('#skF_4','#skF_1')
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_14,c_106])).

tff(c_118,plain,(
    v1_partfun1('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_16,c_109])).

tff(c_120,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_118])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:03:14 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.74/1.16  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.74/1.17  
% 1.74/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.74/1.17  %$ v1_funct_2 > v1_partfun1 > r1_partfun1 > m1_subset_1 > v1_funct_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.74/1.17  
% 1.74/1.17  %Foreground sorts:
% 1.74/1.17  
% 1.74/1.17  
% 1.74/1.17  %Background operators:
% 1.74/1.17  
% 1.74/1.17  
% 1.74/1.17  %Foreground operators:
% 1.74/1.17  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.74/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.74/1.17  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.74/1.17  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 1.74/1.17  tff('#skF_2', type, '#skF_2': $i).
% 1.74/1.17  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 1.74/1.17  tff('#skF_3', type, '#skF_3': $i).
% 1.74/1.17  tff('#skF_1', type, '#skF_1': $i).
% 1.74/1.17  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.74/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.74/1.17  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.74/1.17  tff('#skF_4', type, '#skF_4': $i).
% 1.74/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.74/1.17  tff(r1_partfun1, type, r1_partfun1: ($i * $i) > $o).
% 1.74/1.17  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.74/1.17  
% 1.99/1.18  tff(f_87, negated_conjecture, ~(![A, B]: ((v1_funct_1(B) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (![C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => ((r1_partfun1(B, D) & r1_partfun1(C, D)) => r1_partfun1(B, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_funct_2)).
% 1.99/1.18  tff(f_42, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | v1_partfun1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t132_funct_2)).
% 1.99/1.18  tff(f_64, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: ((v1_funct_1(D) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((r1_partfun1(C, E) & r1_partfun1(D, E)) & v1_partfun1(E, A)) => r1_partfun1(C, D)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t158_partfun1)).
% 1.99/1.18  tff(c_8, plain, (~r1_partfun1('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_87])).
% 1.99/1.18  tff(c_26, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_87])).
% 1.99/1.18  tff(c_12, plain, (r1_partfun1('#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_87])).
% 1.99/1.18  tff(c_24, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_87])).
% 1.99/1.18  tff(c_14, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_87])).
% 1.99/1.18  tff(c_18, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_87])).
% 1.99/1.18  tff(c_16, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_87])).
% 1.99/1.18  tff(c_28, plain, (![B_19, C_20, A_21]: (k1_xboole_0=B_19 | v1_partfun1(C_20, A_21) | ~v1_funct_2(C_20, A_21, B_19) | ~m1_subset_1(C_20, k1_zfmisc_1(k2_zfmisc_1(A_21, B_19))) | ~v1_funct_1(C_20))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.99/1.18  tff(c_31, plain, (k1_xboole_0='#skF_1' | v1_partfun1('#skF_4', '#skF_1') | ~v1_funct_2('#skF_4', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_14, c_28])).
% 1.99/1.18  tff(c_40, plain, (k1_xboole_0='#skF_1' | v1_partfun1('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_16, c_31])).
% 1.99/1.18  tff(c_47, plain, (v1_partfun1('#skF_4', '#skF_1')), inference(splitLeft, [status(thm)], [c_40])).
% 1.99/1.18  tff(c_20, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_87])).
% 1.99/1.18  tff(c_22, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_87])).
% 1.99/1.18  tff(c_10, plain, (r1_partfun1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_87])).
% 1.99/1.18  tff(c_49, plain, (![E_25, A_26, D_22, B_23, C_24]: (r1_partfun1(C_24, D_22) | ~v1_partfun1(E_25, A_26) | ~r1_partfun1(D_22, E_25) | ~r1_partfun1(C_24, E_25) | ~m1_subset_1(E_25, k1_zfmisc_1(k2_zfmisc_1(A_26, B_23))) | ~v1_funct_1(E_25) | ~m1_subset_1(D_22, k1_zfmisc_1(k2_zfmisc_1(A_26, B_23))) | ~v1_funct_1(D_22) | ~m1_subset_1(C_24, k1_zfmisc_1(k2_zfmisc_1(A_26, B_23))) | ~v1_funct_1(C_24))), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.99/1.18  tff(c_51, plain, (![C_24, A_26, B_23]: (r1_partfun1(C_24, '#skF_3') | ~v1_partfun1('#skF_4', A_26) | ~r1_partfun1(C_24, '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_26, B_23))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_26, B_23))) | ~v1_funct_1('#skF_3') | ~m1_subset_1(C_24, k1_zfmisc_1(k2_zfmisc_1(A_26, B_23))) | ~v1_funct_1(C_24))), inference(resolution, [status(thm)], [c_10, c_49])).
% 1.99/1.18  tff(c_61, plain, (![C_27, A_28, B_29]: (r1_partfun1(C_27, '#skF_3') | ~v1_partfun1('#skF_4', A_28) | ~r1_partfun1(C_27, '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_28, B_29))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_28, B_29))) | ~m1_subset_1(C_27, k1_zfmisc_1(k2_zfmisc_1(A_28, B_29))) | ~v1_funct_1(C_27))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_18, c_51])).
% 1.99/1.18  tff(c_63, plain, (![C_27]: (r1_partfun1(C_27, '#skF_3') | ~v1_partfun1('#skF_4', '#skF_1') | ~r1_partfun1(C_27, '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(C_27, k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_1(C_27))), inference(resolution, [status(thm)], [c_20, c_61])).
% 1.99/1.18  tff(c_67, plain, (![C_30]: (r1_partfun1(C_30, '#skF_3') | ~r1_partfun1(C_30, '#skF_4') | ~m1_subset_1(C_30, k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_1(C_30))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_47, c_63])).
% 1.99/1.18  tff(c_73, plain, (r1_partfun1('#skF_2', '#skF_3') | ~r1_partfun1('#skF_2', '#skF_4') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_24, c_67])).
% 1.99/1.18  tff(c_82, plain, (r1_partfun1('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_12, c_73])).
% 1.99/1.18  tff(c_84, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8, c_82])).
% 1.99/1.18  tff(c_86, plain, (~v1_partfun1('#skF_4', '#skF_1')), inference(splitRight, [status(thm)], [c_40])).
% 1.99/1.18  tff(c_85, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_40])).
% 1.99/1.18  tff(c_2, plain, (![C_3, B_2]: (v1_partfun1(C_3, k1_xboole_0) | ~v1_funct_2(C_3, k1_xboole_0, B_2) | ~m1_subset_1(C_3, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_2))) | ~v1_funct_1(C_3))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.99/1.18  tff(c_106, plain, (![C_36, B_37]: (v1_partfun1(C_36, '#skF_1') | ~v1_funct_2(C_36, '#skF_1', B_37) | ~m1_subset_1(C_36, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_37))) | ~v1_funct_1(C_36))), inference(demodulation, [status(thm), theory('equality')], [c_85, c_85, c_85, c_2])).
% 1.99/1.18  tff(c_109, plain, (v1_partfun1('#skF_4', '#skF_1') | ~v1_funct_2('#skF_4', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_14, c_106])).
% 1.99/1.18  tff(c_118, plain, (v1_partfun1('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_16, c_109])).
% 1.99/1.18  tff(c_120, plain, $false, inference(negUnitSimplification, [status(thm)], [c_86, c_118])).
% 1.99/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.99/1.18  
% 1.99/1.18  Inference rules
% 1.99/1.18  ----------------------
% 1.99/1.18  #Ref     : 0
% 1.99/1.18  #Sup     : 16
% 1.99/1.18  #Fact    : 0
% 1.99/1.18  #Define  : 0
% 1.99/1.18  #Split   : 3
% 1.99/1.18  #Chain   : 0
% 1.99/1.18  #Close   : 0
% 1.99/1.18  
% 1.99/1.18  Ordering : KBO
% 1.99/1.18  
% 1.99/1.18  Simplification rules
% 1.99/1.18  ----------------------
% 1.99/1.18  #Subsume      : 0
% 1.99/1.18  #Demod        : 25
% 1.99/1.18  #Tautology    : 4
% 1.99/1.18  #SimpNegUnit  : 2
% 1.99/1.18  #BackRed      : 2
% 1.99/1.18  
% 1.99/1.18  #Partial instantiations: 0
% 1.99/1.18  #Strategies tried      : 1
% 1.99/1.18  
% 1.99/1.18  Timing (in seconds)
% 1.99/1.18  ----------------------
% 1.99/1.18  Preprocessing        : 0.28
% 1.99/1.18  Parsing              : 0.16
% 1.99/1.18  CNF conversion       : 0.02
% 1.99/1.18  Main loop            : 0.14
% 1.99/1.18  Inferencing          : 0.06
% 1.99/1.18  Reduction            : 0.04
% 1.99/1.18  Demodulation         : 0.03
% 1.99/1.18  BG Simplification    : 0.01
% 1.99/1.18  Subsumption          : 0.02
% 1.99/1.19  Abstraction          : 0.01
% 1.99/1.19  MUC search           : 0.00
% 1.99/1.19  Cooper               : 0.00
% 1.99/1.19  Total                : 0.45
% 1.99/1.19  Index Insertion      : 0.00
% 1.99/1.19  Index Deletion       : 0.00
% 1.99/1.19  Index Matching       : 0.00
% 1.99/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
