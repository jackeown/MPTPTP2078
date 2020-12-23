%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:54 EST 2020

% Result     : Theorem 1.70s
% Output     : CNFRefutation 1.92s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 155 expanded)
%              Number of leaves         :   27 (  67 expanded)
%              Depth                    :    9
%              Number of atoms          :   61 ( 204 expanded)
%              Number of equality atoms :   24 (  94 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_xboole_0 > v1_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_6 > #skF_3 > #skF_1 > #skF_7 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_31,axiom,(
    ? [A] : v1_xboole_0(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_xboole_0)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_73,negated_conjecture,(
    ~ ( k1_relat_1(k1_xboole_0) = k1_xboole_0
      & k2_relat_1(k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_39,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_60,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_48,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_52,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ~ ( r2_hidden(A,k2_relat_1(B))
          & ! [C] : ~ r2_hidden(C,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_relat_1)).

tff(c_4,plain,(
    v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_40,plain,(
    ! [A_32] :
      ( k1_xboole_0 = A_32
      | ~ v1_xboole_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_44,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_4,c_40])).

tff(c_32,plain,
    ( k2_relat_1(k1_xboole_0) != k1_xboole_0
    | k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_85,plain,
    ( k2_relat_1('#skF_1') != '#skF_1'
    | k1_relat_1('#skF_1') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_44,c_44,c_44,c_32])).

tff(c_86,plain,(
    k1_relat_1('#skF_1') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_85])).

tff(c_6,plain,(
    ! [A_2] :
      ( r2_hidden('#skF_2'(A_2),A_2)
      | k1_xboole_0 = A_2 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_95,plain,(
    ! [A_2] :
      ( r2_hidden('#skF_2'(A_2),A_2)
      | A_2 = '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_6])).

tff(c_117,plain,(
    ! [C_48,A_49] :
      ( r2_hidden(k4_tarski(C_48,'#skF_6'(A_49,k1_relat_1(A_49),C_48)),A_49)
      | ~ r2_hidden(C_48,k1_relat_1(A_49)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_10,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_56,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_44,c_10])).

tff(c_87,plain,(
    ! [A_37,B_38] : ~ r2_hidden(A_37,k2_zfmisc_1(A_37,B_38)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_93,plain,(
    ! [A_4] : ~ r2_hidden(A_4,'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_87])).

tff(c_128,plain,(
    ! [C_52] : ~ r2_hidden(C_52,k1_relat_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_117,c_93])).

tff(c_140,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_95,c_128])).

tff(c_148,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_140])).

tff(c_149,plain,(
    k2_relat_1('#skF_1') != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_85])).

tff(c_162,plain,(
    ! [A_2] :
      ( r2_hidden('#skF_2'(A_2),A_2)
      | A_2 = '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_6])).

tff(c_155,plain,(
    ! [A_53,B_54] : ~ r2_hidden(A_53,k2_zfmisc_1(A_53,B_54)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_161,plain,(
    ! [A_4] : ~ r2_hidden(A_4,'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_155])).

tff(c_51,plain,(
    ! [A_33] :
      ( v1_relat_1(A_33)
      | ~ v1_xboole_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_55,plain,(
    v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_4,c_51])).

tff(c_150,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_85])).

tff(c_184,plain,(
    ! [A_62,B_63] :
      ( r2_hidden('#skF_7'(A_62,B_63),k1_relat_1(B_63))
      | ~ r2_hidden(A_62,k2_relat_1(B_63))
      | ~ v1_relat_1(B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_187,plain,(
    ! [A_62] :
      ( r2_hidden('#skF_7'(A_62,'#skF_1'),'#skF_1')
      | ~ r2_hidden(A_62,k2_relat_1('#skF_1'))
      | ~ v1_relat_1('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_150,c_184])).

tff(c_189,plain,(
    ! [A_62] :
      ( r2_hidden('#skF_7'(A_62,'#skF_1'),'#skF_1')
      | ~ r2_hidden(A_62,k2_relat_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_187])).

tff(c_191,plain,(
    ! [A_64] : ~ r2_hidden(A_64,k2_relat_1('#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_161,c_189])).

tff(c_195,plain,(
    k2_relat_1('#skF_1') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_162,c_191])).

tff(c_199,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_149,c_195])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n010.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 13:54:59 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.70/1.18  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.92/1.18  
% 1.92/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.92/1.18  %$ r2_hidden > v1_xboole_0 > v1_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_6 > #skF_3 > #skF_1 > #skF_7 > #skF_5 > #skF_4
% 1.92/1.18  
% 1.92/1.18  %Foreground sorts:
% 1.92/1.18  
% 1.92/1.18  
% 1.92/1.18  %Background operators:
% 1.92/1.18  
% 1.92/1.18  
% 1.92/1.18  %Foreground operators:
% 1.92/1.18  tff('#skF_2', type, '#skF_2': $i > $i).
% 1.92/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.92/1.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.92/1.18  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 1.92/1.18  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.92/1.18  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.92/1.18  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.92/1.18  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.92/1.18  tff('#skF_1', type, '#skF_1': $i).
% 1.92/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.92/1.18  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.92/1.18  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.92/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.92/1.18  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 1.92/1.18  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.92/1.18  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 1.92/1.18  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.92/1.18  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 1.92/1.18  
% 1.92/1.19  tff(f_31, axiom, (?[A]: v1_xboole_0(A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc1_xboole_0)).
% 1.92/1.19  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 1.92/1.19  tff(f_73, negated_conjecture, ~((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 1.92/1.19  tff(f_39, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 1.92/1.19  tff(f_60, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 1.92/1.19  tff(f_45, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 1.92/1.19  tff(f_48, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 1.92/1.19  tff(f_52, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 1.92/1.19  tff(f_69, axiom, (![A, B]: (v1_relat_1(B) => ~(r2_hidden(A, k2_relat_1(B)) & (![C]: ~r2_hidden(C, k1_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_relat_1)).
% 1.92/1.19  tff(c_4, plain, (v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.92/1.19  tff(c_40, plain, (![A_32]: (k1_xboole_0=A_32 | ~v1_xboole_0(A_32))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.92/1.19  tff(c_44, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_4, c_40])).
% 1.92/1.19  tff(c_32, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0 | k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_73])).
% 1.92/1.19  tff(c_85, plain, (k2_relat_1('#skF_1')!='#skF_1' | k1_relat_1('#skF_1')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_44, c_44, c_44, c_44, c_32])).
% 1.92/1.19  tff(c_86, plain, (k1_relat_1('#skF_1')!='#skF_1'), inference(splitLeft, [status(thm)], [c_85])).
% 1.92/1.19  tff(c_6, plain, (![A_2]: (r2_hidden('#skF_2'(A_2), A_2) | k1_xboole_0=A_2)), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.92/1.19  tff(c_95, plain, (![A_2]: (r2_hidden('#skF_2'(A_2), A_2) | A_2='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_6])).
% 1.92/1.19  tff(c_117, plain, (![C_48, A_49]: (r2_hidden(k4_tarski(C_48, '#skF_6'(A_49, k1_relat_1(A_49), C_48)), A_49) | ~r2_hidden(C_48, k1_relat_1(A_49)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.92/1.19  tff(c_10, plain, (![A_4]: (k2_zfmisc_1(A_4, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.92/1.19  tff(c_56, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_44, c_10])).
% 1.92/1.19  tff(c_87, plain, (![A_37, B_38]: (~r2_hidden(A_37, k2_zfmisc_1(A_37, B_38)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.92/1.19  tff(c_93, plain, (![A_4]: (~r2_hidden(A_4, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_56, c_87])).
% 1.92/1.19  tff(c_128, plain, (![C_52]: (~r2_hidden(C_52, k1_relat_1('#skF_1')))), inference(resolution, [status(thm)], [c_117, c_93])).
% 1.92/1.19  tff(c_140, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(resolution, [status(thm)], [c_95, c_128])).
% 1.92/1.19  tff(c_148, plain, $false, inference(negUnitSimplification, [status(thm)], [c_86, c_140])).
% 1.92/1.19  tff(c_149, plain, (k2_relat_1('#skF_1')!='#skF_1'), inference(splitRight, [status(thm)], [c_85])).
% 1.92/1.19  tff(c_162, plain, (![A_2]: (r2_hidden('#skF_2'(A_2), A_2) | A_2='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_6])).
% 1.92/1.19  tff(c_155, plain, (![A_53, B_54]: (~r2_hidden(A_53, k2_zfmisc_1(A_53, B_54)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.92/1.19  tff(c_161, plain, (![A_4]: (~r2_hidden(A_4, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_56, c_155])).
% 1.92/1.19  tff(c_51, plain, (![A_33]: (v1_relat_1(A_33) | ~v1_xboole_0(A_33))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.92/1.19  tff(c_55, plain, (v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_4, c_51])).
% 1.92/1.19  tff(c_150, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(splitRight, [status(thm)], [c_85])).
% 1.92/1.19  tff(c_184, plain, (![A_62, B_63]: (r2_hidden('#skF_7'(A_62, B_63), k1_relat_1(B_63)) | ~r2_hidden(A_62, k2_relat_1(B_63)) | ~v1_relat_1(B_63))), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.92/1.19  tff(c_187, plain, (![A_62]: (r2_hidden('#skF_7'(A_62, '#skF_1'), '#skF_1') | ~r2_hidden(A_62, k2_relat_1('#skF_1')) | ~v1_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_150, c_184])).
% 1.92/1.19  tff(c_189, plain, (![A_62]: (r2_hidden('#skF_7'(A_62, '#skF_1'), '#skF_1') | ~r2_hidden(A_62, k2_relat_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_55, c_187])).
% 1.92/1.19  tff(c_191, plain, (![A_64]: (~r2_hidden(A_64, k2_relat_1('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_161, c_189])).
% 1.92/1.19  tff(c_195, plain, (k2_relat_1('#skF_1')='#skF_1'), inference(resolution, [status(thm)], [c_162, c_191])).
% 1.92/1.19  tff(c_199, plain, $false, inference(negUnitSimplification, [status(thm)], [c_149, c_195])).
% 1.92/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.92/1.19  
% 1.92/1.19  Inference rules
% 1.92/1.19  ----------------------
% 1.92/1.19  #Ref     : 0
% 1.92/1.19  #Sup     : 32
% 1.92/1.19  #Fact    : 0
% 1.92/1.19  #Define  : 0
% 1.92/1.19  #Split   : 1
% 1.92/1.19  #Chain   : 0
% 1.92/1.19  #Close   : 0
% 1.92/1.19  
% 1.92/1.19  Ordering : KBO
% 1.92/1.19  
% 1.92/1.19  Simplification rules
% 1.92/1.19  ----------------------
% 1.92/1.19  #Subsume      : 2
% 1.92/1.19  #Demod        : 19
% 1.92/1.19  #Tautology    : 20
% 1.92/1.19  #SimpNegUnit  : 3
% 1.92/1.19  #BackRed      : 2
% 1.92/1.20  
% 1.92/1.20  #Partial instantiations: 0
% 1.92/1.20  #Strategies tried      : 1
% 1.92/1.20  
% 1.92/1.20  Timing (in seconds)
% 1.92/1.20  ----------------------
% 1.92/1.20  Preprocessing        : 0.29
% 1.92/1.20  Parsing              : 0.16
% 1.92/1.20  CNF conversion       : 0.02
% 2.00/1.20  Main loop            : 0.16
% 2.00/1.20  Inferencing          : 0.06
% 2.00/1.20  Reduction            : 0.04
% 2.00/1.20  Demodulation         : 0.03
% 2.00/1.20  BG Simplification    : 0.01
% 2.00/1.20  Subsumption          : 0.02
% 2.00/1.20  Abstraction          : 0.01
% 2.00/1.20  MUC search           : 0.00
% 2.00/1.20  Cooper               : 0.00
% 2.00/1.20  Total                : 0.47
% 2.00/1.20  Index Insertion      : 0.00
% 2.00/1.20  Index Deletion       : 0.00
% 2.00/1.20  Index Matching       : 0.00
% 2.00/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
