%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:13 EST 2020

% Result     : Theorem 1.96s
% Output     : CNFRefutation 1.96s
% Verified   : 
% Statistics : Number of formulae       :   43 (  66 expanded)
%              Number of leaves         :   20 (  33 expanded)
%              Depth                    :    9
%              Number of atoms          :   59 ( 143 expanded)
%              Number of equality atoms :    5 (   9 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_setfam_1 > r2_hidden > m1_subset_1 > v1_xboole_0 > k4_subset_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v3_setfam_1,type,(
    v3_setfam_1: ( $i * $i ) > $o )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_69,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ( v3_setfam_1(B,A)
              & m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A))) )
           => ! [C] :
                ( ( v3_setfam_1(C,A)
                  & m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A))) )
               => v3_setfam_1(k4_subset_1(k1_zfmisc_1(A),B,C),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_setfam_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( v3_setfam_1(B,A)
      <=> ~ r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_setfam_1)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => m1_subset_1(k4_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_subset_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

tff(c_36,plain,(
    v3_setfam_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_34,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_61,plain,(
    ! [A_30,B_31] :
      ( ~ r2_hidden(A_30,B_31)
      | ~ v3_setfam_1(B_31,A_30)
      | ~ m1_subset_1(B_31,k1_zfmisc_1(k1_zfmisc_1(A_30))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_64,plain,
    ( ~ r2_hidden('#skF_3','#skF_4')
    | ~ v3_setfam_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_61])).

tff(c_70,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_64])).

tff(c_32,plain,(
    v3_setfam_1('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_30,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_67,plain,
    ( ~ r2_hidden('#skF_3','#skF_5')
    | ~ v3_setfam_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_61])).

tff(c_73,plain,(
    ~ r2_hidden('#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_67])).

tff(c_74,plain,(
    ! [A_32,B_33,C_34] :
      ( k4_subset_1(A_32,B_33,C_34) = k2_xboole_0(B_33,C_34)
      | ~ m1_subset_1(C_34,k1_zfmisc_1(A_32))
      | ~ m1_subset_1(B_33,k1_zfmisc_1(A_32)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_142,plain,(
    ! [B_39] :
      ( k4_subset_1(k1_zfmisc_1('#skF_3'),B_39,'#skF_5') = k2_xboole_0(B_39,'#skF_5')
      | ~ m1_subset_1(B_39,k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ) ),
    inference(resolution,[status(thm)],[c_30,c_74])).

tff(c_158,plain,(
    k4_subset_1(k1_zfmisc_1('#skF_3'),'#skF_4','#skF_5') = k2_xboole_0('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_34,c_142])).

tff(c_28,plain,(
    ~ v3_setfam_1(k4_subset_1(k1_zfmisc_1('#skF_3'),'#skF_4','#skF_5'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_179,plain,(
    ~ v3_setfam_1(k2_xboole_0('#skF_4','#skF_5'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_28])).

tff(c_20,plain,(
    ! [A_7,B_8,C_9] :
      ( m1_subset_1(k4_subset_1(A_7,B_8,C_9),k1_zfmisc_1(A_7))
      | ~ m1_subset_1(C_9,k1_zfmisc_1(A_7))
      | ~ m1_subset_1(B_8,k1_zfmisc_1(A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_183,plain,
    ( m1_subset_1(k2_xboole_0('#skF_4','#skF_5'),k1_zfmisc_1(k1_zfmisc_1('#skF_3')))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1('#skF_3')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_158,c_20])).

tff(c_187,plain,(
    m1_subset_1(k2_xboole_0('#skF_4','#skF_5'),k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_183])).

tff(c_24,plain,(
    ! [B_14,A_13] :
      ( v3_setfam_1(B_14,A_13)
      | r2_hidden(A_13,B_14)
      | ~ m1_subset_1(B_14,k1_zfmisc_1(k1_zfmisc_1(A_13))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_202,plain,
    ( v3_setfam_1(k2_xboole_0('#skF_4','#skF_5'),'#skF_3')
    | r2_hidden('#skF_3',k2_xboole_0('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_187,c_24])).

tff(c_209,plain,(
    r2_hidden('#skF_3',k2_xboole_0('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_179,c_202])).

tff(c_2,plain,(
    ! [D_6,B_2,A_1] :
      ( r2_hidden(D_6,B_2)
      | r2_hidden(D_6,A_1)
      | ~ r2_hidden(D_6,k2_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_212,plain,
    ( r2_hidden('#skF_3','#skF_5')
    | r2_hidden('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_209,c_2])).

tff(c_216,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_73,c_212])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:27:40 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.96/1.22  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.96/1.23  
% 1.96/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.96/1.23  %$ v3_setfam_1 > r2_hidden > m1_subset_1 > v1_xboole_0 > k4_subset_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4
% 1.96/1.23  
% 1.96/1.23  %Foreground sorts:
% 1.96/1.23  
% 1.96/1.23  
% 1.96/1.23  %Background operators:
% 1.96/1.23  
% 1.96/1.23  
% 1.96/1.23  %Foreground operators:
% 1.96/1.23  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.96/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.96/1.23  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.96/1.23  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 1.96/1.23  tff('#skF_5', type, '#skF_5': $i).
% 1.96/1.23  tff('#skF_3', type, '#skF_3': $i).
% 1.96/1.23  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.96/1.23  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.96/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.96/1.23  tff('#skF_4', type, '#skF_4': $i).
% 1.96/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.96/1.23  tff(v3_setfam_1, type, v3_setfam_1: ($i * $i) > $o).
% 1.96/1.23  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.96/1.23  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.96/1.23  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.96/1.23  
% 1.96/1.24  tff(f_69, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: ((v3_setfam_1(B, A) & m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A)))) => (![C]: ((v3_setfam_1(C, A) & m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A)))) => v3_setfam_1(k4_subset_1(k1_zfmisc_1(A), B, C), A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_setfam_1)).
% 1.96/1.24  tff(f_53, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (v3_setfam_1(B, A) <=> ~r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d13_setfam_1)).
% 1.96/1.24  tff(f_46, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 1.96/1.24  tff(f_40, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => m1_subset_1(k4_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_subset_1)).
% 1.96/1.24  tff(f_34, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 1.96/1.24  tff(c_36, plain, (v3_setfam_1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.96/1.24  tff(c_34, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.96/1.24  tff(c_61, plain, (![A_30, B_31]: (~r2_hidden(A_30, B_31) | ~v3_setfam_1(B_31, A_30) | ~m1_subset_1(B_31, k1_zfmisc_1(k1_zfmisc_1(A_30))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.96/1.24  tff(c_64, plain, (~r2_hidden('#skF_3', '#skF_4') | ~v3_setfam_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_34, c_61])).
% 1.96/1.24  tff(c_70, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_64])).
% 1.96/1.24  tff(c_32, plain, (v3_setfam_1('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.96/1.24  tff(c_30, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k1_zfmisc_1('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.96/1.24  tff(c_67, plain, (~r2_hidden('#skF_3', '#skF_5') | ~v3_setfam_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_30, c_61])).
% 1.96/1.24  tff(c_73, plain, (~r2_hidden('#skF_3', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_67])).
% 1.96/1.24  tff(c_74, plain, (![A_32, B_33, C_34]: (k4_subset_1(A_32, B_33, C_34)=k2_xboole_0(B_33, C_34) | ~m1_subset_1(C_34, k1_zfmisc_1(A_32)) | ~m1_subset_1(B_33, k1_zfmisc_1(A_32)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.96/1.24  tff(c_142, plain, (![B_39]: (k4_subset_1(k1_zfmisc_1('#skF_3'), B_39, '#skF_5')=k2_xboole_0(B_39, '#skF_5') | ~m1_subset_1(B_39, k1_zfmisc_1(k1_zfmisc_1('#skF_3'))))), inference(resolution, [status(thm)], [c_30, c_74])).
% 1.96/1.24  tff(c_158, plain, (k4_subset_1(k1_zfmisc_1('#skF_3'), '#skF_4', '#skF_5')=k2_xboole_0('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_34, c_142])).
% 1.96/1.24  tff(c_28, plain, (~v3_setfam_1(k4_subset_1(k1_zfmisc_1('#skF_3'), '#skF_4', '#skF_5'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.96/1.24  tff(c_179, plain, (~v3_setfam_1(k2_xboole_0('#skF_4', '#skF_5'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_158, c_28])).
% 1.96/1.24  tff(c_20, plain, (![A_7, B_8, C_9]: (m1_subset_1(k4_subset_1(A_7, B_8, C_9), k1_zfmisc_1(A_7)) | ~m1_subset_1(C_9, k1_zfmisc_1(A_7)) | ~m1_subset_1(B_8, k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.96/1.24  tff(c_183, plain, (m1_subset_1(k2_xboole_0('#skF_4', '#skF_5'), k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_158, c_20])).
% 1.96/1.24  tff(c_187, plain, (m1_subset_1(k2_xboole_0('#skF_4', '#skF_5'), k1_zfmisc_1(k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_183])).
% 1.96/1.24  tff(c_24, plain, (![B_14, A_13]: (v3_setfam_1(B_14, A_13) | r2_hidden(A_13, B_14) | ~m1_subset_1(B_14, k1_zfmisc_1(k1_zfmisc_1(A_13))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.96/1.24  tff(c_202, plain, (v3_setfam_1(k2_xboole_0('#skF_4', '#skF_5'), '#skF_3') | r2_hidden('#skF_3', k2_xboole_0('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_187, c_24])).
% 1.96/1.24  tff(c_209, plain, (r2_hidden('#skF_3', k2_xboole_0('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_179, c_202])).
% 1.96/1.24  tff(c_2, plain, (![D_6, B_2, A_1]: (r2_hidden(D_6, B_2) | r2_hidden(D_6, A_1) | ~r2_hidden(D_6, k2_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.96/1.24  tff(c_212, plain, (r2_hidden('#skF_3', '#skF_5') | r2_hidden('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_209, c_2])).
% 1.96/1.24  tff(c_216, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_73, c_212])).
% 1.96/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.96/1.24  
% 1.96/1.24  Inference rules
% 1.96/1.24  ----------------------
% 1.96/1.24  #Ref     : 0
% 1.96/1.24  #Sup     : 42
% 1.96/1.24  #Fact    : 0
% 1.96/1.24  #Define  : 0
% 1.96/1.24  #Split   : 0
% 1.96/1.24  #Chain   : 0
% 1.96/1.24  #Close   : 0
% 1.96/1.24  
% 1.96/1.24  Ordering : KBO
% 1.96/1.24  
% 1.96/1.24  Simplification rules
% 1.96/1.24  ----------------------
% 1.96/1.24  #Subsume      : 1
% 1.96/1.24  #Demod        : 11
% 1.96/1.24  #Tautology    : 10
% 1.96/1.24  #SimpNegUnit  : 2
% 1.96/1.24  #BackRed      : 1
% 1.96/1.24  
% 1.96/1.24  #Partial instantiations: 0
% 1.96/1.24  #Strategies tried      : 1
% 1.96/1.24  
% 1.96/1.24  Timing (in seconds)
% 1.96/1.24  ----------------------
% 1.96/1.24  Preprocessing        : 0.29
% 1.96/1.24  Parsing              : 0.15
% 1.96/1.24  CNF conversion       : 0.02
% 1.96/1.24  Main loop            : 0.16
% 1.96/1.24  Inferencing          : 0.05
% 1.96/1.24  Reduction            : 0.05
% 1.96/1.24  Demodulation         : 0.04
% 1.96/1.24  BG Simplification    : 0.01
% 1.96/1.24  Subsumption          : 0.03
% 1.96/1.24  Abstraction          : 0.01
% 1.96/1.24  MUC search           : 0.00
% 1.96/1.24  Cooper               : 0.00
% 1.96/1.24  Total                : 0.48
% 1.96/1.24  Index Insertion      : 0.00
% 1.96/1.24  Index Deletion       : 0.00
% 1.96/1.24  Index Matching       : 0.00
% 1.96/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
