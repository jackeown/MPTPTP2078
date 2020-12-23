%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:21 EST 2020

% Result     : Theorem 2.04s
% Output     : CNFRefutation 2.04s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 142 expanded)
%              Number of leaves         :   26 (  59 expanded)
%              Depth                    :   10
%              Number of atoms          :   97 ( 287 expanded)
%              Number of equality atoms :   18 (  62 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k3_xboole_0 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_6 > #skF_4 > #skF_1 > #skF_7 > #skF_2 > #skF_8 > #skF_3 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_88,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ~ ( B != k1_xboole_0
            & ! [C] :
                ( m1_subset_1(C,A)
               => ~ r2_hidden(C,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_subset_1)).

tff(f_48,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_72,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_75,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(c_52,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_24,plain,(
    ! [A_11] :
      ( r2_hidden('#skF_4'(A_11),A_11)
      | k1_xboole_0 = A_11 ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_62,plain,(
    ! [C_29] :
      ( ~ r2_hidden(C_29,'#skF_8')
      | ~ m1_subset_1(C_29,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_66,plain,
    ( ~ m1_subset_1('#skF_4'('#skF_8'),'#skF_7')
    | k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_24,c_62])).

tff(c_69,plain,(
    ~ m1_subset_1('#skF_4'('#skF_8'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_66])).

tff(c_110,plain,(
    ! [B_40,A_41] :
      ( m1_subset_1(B_40,A_41)
      | ~ v1_xboole_0(B_40)
      | ~ v1_xboole_0(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_122,plain,
    ( ~ v1_xboole_0('#skF_4'('#skF_8'))
    | ~ v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_110,c_69])).

tff(c_128,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_122])).

tff(c_54,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_48,plain,(
    ! [A_22] : ~ v1_xboole_0(k1_zfmisc_1(A_22)) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_140,plain,(
    ! [B_46,A_47] :
      ( r2_hidden(B_46,A_47)
      | ~ m1_subset_1(B_46,A_47)
      | v1_xboole_0(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_28,plain,(
    ! [C_19,A_15] :
      ( r1_tarski(C_19,A_15)
      | ~ r2_hidden(C_19,k1_zfmisc_1(A_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_148,plain,(
    ! [B_46,A_15] :
      ( r1_tarski(B_46,A_15)
      | ~ m1_subset_1(B_46,k1_zfmisc_1(A_15))
      | v1_xboole_0(k1_zfmisc_1(A_15)) ) ),
    inference(resolution,[status(thm)],[c_140,c_28])).

tff(c_162,plain,(
    ! [B_48,A_49] :
      ( r1_tarski(B_48,A_49)
      | ~ m1_subset_1(B_48,k1_zfmisc_1(A_49)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_148])).

tff(c_171,plain,(
    r1_tarski('#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_54,c_162])).

tff(c_26,plain,(
    ! [A_13,B_14] :
      ( k3_xboole_0(A_13,B_14) = A_13
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_175,plain,(
    k3_xboole_0('#skF_8','#skF_7') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_171,c_26])).

tff(c_8,plain,(
    ! [D_10,B_6,A_5] :
      ( r2_hidden(D_10,B_6)
      | ~ r2_hidden(D_10,k3_xboole_0(A_5,B_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_214,plain,(
    ! [D_53] :
      ( r2_hidden(D_53,'#skF_7')
      | ~ r2_hidden(D_53,'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_175,c_8])).

tff(c_40,plain,(
    ! [B_21,A_20] :
      ( m1_subset_1(B_21,A_20)
      | ~ r2_hidden(B_21,A_20)
      | v1_xboole_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_217,plain,(
    ! [D_53] :
      ( m1_subset_1(D_53,'#skF_7')
      | v1_xboole_0('#skF_7')
      | ~ r2_hidden(D_53,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_214,c_40])).

tff(c_225,plain,(
    ! [D_54] :
      ( m1_subset_1(D_54,'#skF_7')
      | ~ r2_hidden(D_54,'#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_128,c_217])).

tff(c_237,plain,
    ( m1_subset_1('#skF_4'('#skF_8'),'#skF_7')
    | k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_24,c_225])).

tff(c_245,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_69,c_237])).

tff(c_247,plain,(
    v1_xboole_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_122])).

tff(c_57,plain,(
    ! [A_28] :
      ( r2_hidden('#skF_4'(A_28),A_28)
      | k1_xboole_0 = A_28 ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_61,plain,(
    ! [A_28] :
      ( ~ v1_xboole_0(A_28)
      | k1_xboole_0 = A_28 ) ),
    inference(resolution,[status(thm)],[c_57,c_2])).

tff(c_251,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_247,c_61])).

tff(c_254,plain,(
    '#skF_7' != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_251,c_52])).

tff(c_253,plain,(
    ! [A_11] :
      ( r2_hidden('#skF_4'(A_11),A_11)
      | A_11 = '#skF_7' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_251,c_24])).

tff(c_319,plain,(
    ! [B_65,A_66] :
      ( r2_hidden(B_65,A_66)
      | ~ m1_subset_1(B_65,A_66)
      | v1_xboole_0(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_330,plain,(
    ! [B_65,A_15] :
      ( r1_tarski(B_65,A_15)
      | ~ m1_subset_1(B_65,k1_zfmisc_1(A_15))
      | v1_xboole_0(k1_zfmisc_1(A_15)) ) ),
    inference(resolution,[status(thm)],[c_319,c_28])).

tff(c_345,plain,(
    ! [B_67,A_68] :
      ( r1_tarski(B_67,A_68)
      | ~ m1_subset_1(B_67,k1_zfmisc_1(A_68)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_330])).

tff(c_365,plain,(
    r1_tarski('#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_54,c_345])).

tff(c_369,plain,(
    k3_xboole_0('#skF_8','#skF_7') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_365,c_26])).

tff(c_377,plain,(
    ! [D_69] :
      ( r2_hidden(D_69,'#skF_7')
      | ~ r2_hidden(D_69,'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_369,c_8])).

tff(c_383,plain,(
    ! [D_69] :
      ( ~ v1_xboole_0('#skF_7')
      | ~ r2_hidden(D_69,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_377,c_2])).

tff(c_408,plain,(
    ! [D_73] : ~ r2_hidden(D_73,'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_247,c_383])).

tff(c_416,plain,(
    '#skF_7' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_253,c_408])).

tff(c_425,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_254,c_416])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:21:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.04/1.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.04/1.28  
% 2.04/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.04/1.28  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k3_xboole_0 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_6 > #skF_4 > #skF_1 > #skF_7 > #skF_2 > #skF_8 > #skF_3 > #skF_5
% 2.04/1.28  
% 2.04/1.28  %Foreground sorts:
% 2.04/1.28  
% 2.04/1.28  
% 2.04/1.28  %Background operators:
% 2.04/1.28  
% 2.04/1.28  
% 2.04/1.28  %Foreground operators:
% 2.04/1.28  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 2.04/1.28  tff('#skF_4', type, '#skF_4': $i > $i).
% 2.04/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.04/1.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.04/1.28  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.04/1.28  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.04/1.28  tff('#skF_7', type, '#skF_7': $i).
% 2.04/1.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.04/1.28  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.04/1.28  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.04/1.28  tff('#skF_8', type, '#skF_8': $i).
% 2.04/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.04/1.28  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.04/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.04/1.28  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.04/1.28  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.04/1.28  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 2.04/1.28  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.04/1.28  
% 2.04/1.29  tff(f_88, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => ~(~(B = k1_xboole_0) & (![C]: (m1_subset_1(C, A) => ~r2_hidden(C, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_subset_1)).
% 2.04/1.29  tff(f_48, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.04/1.29  tff(f_72, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 2.04/1.29  tff(f_75, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 2.04/1.29  tff(f_59, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.04/1.29  tff(f_52, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.04/1.29  tff(f_40, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 2.04/1.29  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.04/1.29  tff(c_52, plain, (k1_xboole_0!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.04/1.29  tff(c_24, plain, (![A_11]: (r2_hidden('#skF_4'(A_11), A_11) | k1_xboole_0=A_11)), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.04/1.29  tff(c_62, plain, (![C_29]: (~r2_hidden(C_29, '#skF_8') | ~m1_subset_1(C_29, '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.04/1.29  tff(c_66, plain, (~m1_subset_1('#skF_4'('#skF_8'), '#skF_7') | k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_24, c_62])).
% 2.04/1.29  tff(c_69, plain, (~m1_subset_1('#skF_4'('#skF_8'), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_52, c_66])).
% 2.04/1.29  tff(c_110, plain, (![B_40, A_41]: (m1_subset_1(B_40, A_41) | ~v1_xboole_0(B_40) | ~v1_xboole_0(A_41))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.04/1.29  tff(c_122, plain, (~v1_xboole_0('#skF_4'('#skF_8')) | ~v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_110, c_69])).
% 2.04/1.29  tff(c_128, plain, (~v1_xboole_0('#skF_7')), inference(splitLeft, [status(thm)], [c_122])).
% 2.04/1.29  tff(c_54, plain, (m1_subset_1('#skF_8', k1_zfmisc_1('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.04/1.29  tff(c_48, plain, (![A_22]: (~v1_xboole_0(k1_zfmisc_1(A_22)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.04/1.29  tff(c_140, plain, (![B_46, A_47]: (r2_hidden(B_46, A_47) | ~m1_subset_1(B_46, A_47) | v1_xboole_0(A_47))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.04/1.29  tff(c_28, plain, (![C_19, A_15]: (r1_tarski(C_19, A_15) | ~r2_hidden(C_19, k1_zfmisc_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.04/1.29  tff(c_148, plain, (![B_46, A_15]: (r1_tarski(B_46, A_15) | ~m1_subset_1(B_46, k1_zfmisc_1(A_15)) | v1_xboole_0(k1_zfmisc_1(A_15)))), inference(resolution, [status(thm)], [c_140, c_28])).
% 2.04/1.29  tff(c_162, plain, (![B_48, A_49]: (r1_tarski(B_48, A_49) | ~m1_subset_1(B_48, k1_zfmisc_1(A_49)))), inference(negUnitSimplification, [status(thm)], [c_48, c_148])).
% 2.04/1.29  tff(c_171, plain, (r1_tarski('#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_54, c_162])).
% 2.04/1.29  tff(c_26, plain, (![A_13, B_14]: (k3_xboole_0(A_13, B_14)=A_13 | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.04/1.29  tff(c_175, plain, (k3_xboole_0('#skF_8', '#skF_7')='#skF_8'), inference(resolution, [status(thm)], [c_171, c_26])).
% 2.04/1.29  tff(c_8, plain, (![D_10, B_6, A_5]: (r2_hidden(D_10, B_6) | ~r2_hidden(D_10, k3_xboole_0(A_5, B_6)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.04/1.29  tff(c_214, plain, (![D_53]: (r2_hidden(D_53, '#skF_7') | ~r2_hidden(D_53, '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_175, c_8])).
% 2.04/1.29  tff(c_40, plain, (![B_21, A_20]: (m1_subset_1(B_21, A_20) | ~r2_hidden(B_21, A_20) | v1_xboole_0(A_20))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.04/1.29  tff(c_217, plain, (![D_53]: (m1_subset_1(D_53, '#skF_7') | v1_xboole_0('#skF_7') | ~r2_hidden(D_53, '#skF_8'))), inference(resolution, [status(thm)], [c_214, c_40])).
% 2.04/1.29  tff(c_225, plain, (![D_54]: (m1_subset_1(D_54, '#skF_7') | ~r2_hidden(D_54, '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_128, c_217])).
% 2.04/1.29  tff(c_237, plain, (m1_subset_1('#skF_4'('#skF_8'), '#skF_7') | k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_24, c_225])).
% 2.04/1.29  tff(c_245, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_69, c_237])).
% 2.04/1.29  tff(c_247, plain, (v1_xboole_0('#skF_7')), inference(splitRight, [status(thm)], [c_122])).
% 2.04/1.29  tff(c_57, plain, (![A_28]: (r2_hidden('#skF_4'(A_28), A_28) | k1_xboole_0=A_28)), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.04/1.29  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.04/1.29  tff(c_61, plain, (![A_28]: (~v1_xboole_0(A_28) | k1_xboole_0=A_28)), inference(resolution, [status(thm)], [c_57, c_2])).
% 2.04/1.29  tff(c_251, plain, (k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_247, c_61])).
% 2.04/1.29  tff(c_254, plain, ('#skF_7'!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_251, c_52])).
% 2.04/1.29  tff(c_253, plain, (![A_11]: (r2_hidden('#skF_4'(A_11), A_11) | A_11='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_251, c_24])).
% 2.04/1.29  tff(c_319, plain, (![B_65, A_66]: (r2_hidden(B_65, A_66) | ~m1_subset_1(B_65, A_66) | v1_xboole_0(A_66))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.04/1.29  tff(c_330, plain, (![B_65, A_15]: (r1_tarski(B_65, A_15) | ~m1_subset_1(B_65, k1_zfmisc_1(A_15)) | v1_xboole_0(k1_zfmisc_1(A_15)))), inference(resolution, [status(thm)], [c_319, c_28])).
% 2.04/1.29  tff(c_345, plain, (![B_67, A_68]: (r1_tarski(B_67, A_68) | ~m1_subset_1(B_67, k1_zfmisc_1(A_68)))), inference(negUnitSimplification, [status(thm)], [c_48, c_330])).
% 2.04/1.29  tff(c_365, plain, (r1_tarski('#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_54, c_345])).
% 2.04/1.29  tff(c_369, plain, (k3_xboole_0('#skF_8', '#skF_7')='#skF_8'), inference(resolution, [status(thm)], [c_365, c_26])).
% 2.04/1.29  tff(c_377, plain, (![D_69]: (r2_hidden(D_69, '#skF_7') | ~r2_hidden(D_69, '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_369, c_8])).
% 2.04/1.29  tff(c_383, plain, (![D_69]: (~v1_xboole_0('#skF_7') | ~r2_hidden(D_69, '#skF_8'))), inference(resolution, [status(thm)], [c_377, c_2])).
% 2.04/1.29  tff(c_408, plain, (![D_73]: (~r2_hidden(D_73, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_247, c_383])).
% 2.04/1.29  tff(c_416, plain, ('#skF_7'='#skF_8'), inference(resolution, [status(thm)], [c_253, c_408])).
% 2.04/1.29  tff(c_425, plain, $false, inference(negUnitSimplification, [status(thm)], [c_254, c_416])).
% 2.04/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.04/1.29  
% 2.04/1.29  Inference rules
% 2.04/1.29  ----------------------
% 2.04/1.29  #Ref     : 0
% 2.04/1.29  #Sup     : 72
% 2.04/1.29  #Fact    : 0
% 2.04/1.29  #Define  : 0
% 2.04/1.29  #Split   : 2
% 2.04/1.29  #Chain   : 0
% 2.04/1.29  #Close   : 0
% 2.04/1.30  
% 2.04/1.30  Ordering : KBO
% 2.04/1.30  
% 2.04/1.30  Simplification rules
% 2.04/1.30  ----------------------
% 2.04/1.30  #Subsume      : 11
% 2.04/1.30  #Demod        : 8
% 2.04/1.30  #Tautology    : 21
% 2.04/1.30  #SimpNegUnit  : 13
% 2.04/1.30  #BackRed      : 3
% 2.04/1.30  
% 2.04/1.30  #Partial instantiations: 0
% 2.04/1.30  #Strategies tried      : 1
% 2.04/1.30  
% 2.04/1.30  Timing (in seconds)
% 2.04/1.30  ----------------------
% 2.04/1.30  Preprocessing        : 0.30
% 2.04/1.30  Parsing              : 0.15
% 2.04/1.30  CNF conversion       : 0.02
% 2.04/1.30  Main loop            : 0.21
% 2.04/1.30  Inferencing          : 0.08
% 2.04/1.30  Reduction            : 0.06
% 2.04/1.30  Demodulation         : 0.03
% 2.04/1.30  BG Simplification    : 0.02
% 2.04/1.30  Subsumption          : 0.04
% 2.04/1.30  Abstraction          : 0.01
% 2.04/1.30  MUC search           : 0.00
% 2.04/1.30  Cooper               : 0.00
% 2.04/1.30  Total                : 0.54
% 2.04/1.30  Index Insertion      : 0.00
% 2.04/1.30  Index Deletion       : 0.00
% 2.04/1.30  Index Matching       : 0.00
% 2.04/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
