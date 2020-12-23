%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:48 EST 2020

% Result     : Theorem 2.50s
% Output     : CNFRefutation 2.50s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 135 expanded)
%              Number of leaves         :   18 (  51 expanded)
%              Depth                    :   10
%              Number of atoms          :   96 ( 321 expanded)
%              Number of equality atoms :    5 (  17 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_74,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ( ! [C] :
              ( m1_subset_1(C,A)
             => r2_hidden(C,B) )
         => A = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_subset_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_44,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_28,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_108,plain,(
    ! [B_43,A_44] :
      ( m1_subset_1(B_43,A_44)
      | ~ r2_hidden(B_43,A_44)
      | v1_xboole_0(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_126,plain,(
    ! [A_1] :
      ( m1_subset_1('#skF_1'(A_1),A_1)
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_108])).

tff(c_41,plain,(
    ! [C_24] :
      ( r2_hidden(C_24,'#skF_4')
      | ~ m1_subset_1(C_24,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_45,plain,(
    ! [C_24] :
      ( ~ v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_24,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_41,c_2])).

tff(c_46,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_45])).

tff(c_30,plain,(
    ! [C_19] :
      ( r2_hidden(C_19,'#skF_4')
      | ~ m1_subset_1(C_19,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_117,plain,(
    ! [C_19] :
      ( m1_subset_1(C_19,'#skF_4')
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_19,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_30,c_108])).

tff(c_137,plain,(
    ! [C_47] :
      ( m1_subset_1(C_47,'#skF_4')
      | ~ m1_subset_1(C_47,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_117])).

tff(c_146,plain,
    ( m1_subset_1('#skF_1'('#skF_3'),'#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_126,c_137])).

tff(c_148,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_146])).

tff(c_22,plain,(
    ! [B_13,A_12] :
      ( m1_subset_1(B_13,A_12)
      | ~ v1_xboole_0(B_13)
      | ~ v1_xboole_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_32,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_253,plain,(
    ! [C_62,A_63,B_64] :
      ( r2_hidden(C_62,A_63)
      | ~ r2_hidden(C_62,B_64)
      | ~ m1_subset_1(B_64,k1_zfmisc_1(A_63)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_302,plain,(
    ! [C_70,A_71] :
      ( r2_hidden(C_70,A_71)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_71))
      | ~ m1_subset_1(C_70,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_30,c_253])).

tff(c_310,plain,(
    ! [C_72] :
      ( r2_hidden(C_72,'#skF_3')
      | ~ m1_subset_1(C_72,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_32,c_302])).

tff(c_324,plain,(
    ! [C_72] :
      ( ~ v1_xboole_0('#skF_3')
      | ~ m1_subset_1(C_72,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_310,c_2])).

tff(c_333,plain,(
    ! [C_73] : ~ m1_subset_1(C_73,'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_324])).

tff(c_341,plain,(
    ! [B_13] :
      ( ~ v1_xboole_0(B_13)
      | ~ v1_xboole_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_22,c_333])).

tff(c_346,plain,(
    ! [B_13] : ~ v1_xboole_0(B_13) ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_341])).

tff(c_357,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_346,c_148])).

tff(c_359,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_146])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_2'(A_5,B_6),A_5)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_466,plain,(
    ! [A_90,B_91] :
      ( m1_subset_1('#skF_2'(A_90,B_91),A_90)
      | v1_xboole_0(A_90)
      | r1_tarski(A_90,B_91) ) ),
    inference(resolution,[status(thm)],[c_10,c_108])).

tff(c_80,plain,(
    ! [A_37,B_38] :
      ( ~ r2_hidden('#skF_2'(A_37,B_38),B_38)
      | r1_tarski(A_37,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_96,plain,(
    ! [A_37] :
      ( r1_tarski(A_37,'#skF_4')
      | ~ m1_subset_1('#skF_2'(A_37,'#skF_4'),'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_30,c_80])).

tff(c_478,plain,
    ( v1_xboole_0('#skF_3')
    | r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_466,c_96])).

tff(c_489,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_359,c_478])).

tff(c_12,plain,(
    ! [B_11,A_10] :
      ( B_11 = A_10
      | ~ r1_tarski(B_11,A_10)
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_498,plain,
    ( '#skF_3' = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_489,c_12])).

tff(c_505,plain,(
    ~ r1_tarski('#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_498])).

tff(c_441,plain,(
    ! [C_85,A_86,B_87] :
      ( r2_hidden(C_85,A_86)
      | ~ r2_hidden(C_85,B_87)
      | ~ m1_subset_1(B_87,k1_zfmisc_1(A_86)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_707,plain,(
    ! [A_117,B_118,A_119] :
      ( r2_hidden('#skF_2'(A_117,B_118),A_119)
      | ~ m1_subset_1(A_117,k1_zfmisc_1(A_119))
      | r1_tarski(A_117,B_118) ) ),
    inference(resolution,[status(thm)],[c_10,c_441])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( ~ r2_hidden('#skF_2'(A_5,B_6),B_6)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_727,plain,(
    ! [A_120,A_121] :
      ( ~ m1_subset_1(A_120,k1_zfmisc_1(A_121))
      | r1_tarski(A_120,A_121) ) ),
    inference(resolution,[status(thm)],[c_707,c_8])).

tff(c_742,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_727])).

tff(c_749,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_505,c_742])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n024.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:57:06 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.50/1.43  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.50/1.43  
% 2.50/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.50/1.43  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 2.50/1.43  
% 2.50/1.43  %Foreground sorts:
% 2.50/1.43  
% 2.50/1.43  
% 2.50/1.43  %Background operators:
% 2.50/1.43  
% 2.50/1.43  
% 2.50/1.43  %Foreground operators:
% 2.50/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.50/1.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.50/1.43  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.50/1.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.50/1.43  tff('#skF_3', type, '#skF_3': $i).
% 2.50/1.43  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.50/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.50/1.43  tff('#skF_4', type, '#skF_4': $i).
% 2.50/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.50/1.43  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.50/1.43  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.50/1.43  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.50/1.43  
% 2.50/1.45  tff(f_74, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => ((![C]: (m1_subset_1(C, A) => r2_hidden(C, B))) => (A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_subset_1)).
% 2.50/1.45  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.50/1.45  tff(f_57, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 2.50/1.45  tff(f_64, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 2.50/1.45  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.50/1.45  tff(f_44, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.50/1.45  tff(c_28, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.50/1.45  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.50/1.45  tff(c_108, plain, (![B_43, A_44]: (m1_subset_1(B_43, A_44) | ~r2_hidden(B_43, A_44) | v1_xboole_0(A_44))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.50/1.45  tff(c_126, plain, (![A_1]: (m1_subset_1('#skF_1'(A_1), A_1) | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_4, c_108])).
% 2.50/1.45  tff(c_41, plain, (![C_24]: (r2_hidden(C_24, '#skF_4') | ~m1_subset_1(C_24, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.50/1.45  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.50/1.45  tff(c_45, plain, (![C_24]: (~v1_xboole_0('#skF_4') | ~m1_subset_1(C_24, '#skF_3'))), inference(resolution, [status(thm)], [c_41, c_2])).
% 2.50/1.45  tff(c_46, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_45])).
% 2.50/1.45  tff(c_30, plain, (![C_19]: (r2_hidden(C_19, '#skF_4') | ~m1_subset_1(C_19, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.50/1.45  tff(c_117, plain, (![C_19]: (m1_subset_1(C_19, '#skF_4') | v1_xboole_0('#skF_4') | ~m1_subset_1(C_19, '#skF_3'))), inference(resolution, [status(thm)], [c_30, c_108])).
% 2.50/1.45  tff(c_137, plain, (![C_47]: (m1_subset_1(C_47, '#skF_4') | ~m1_subset_1(C_47, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_46, c_117])).
% 2.50/1.45  tff(c_146, plain, (m1_subset_1('#skF_1'('#skF_3'), '#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_126, c_137])).
% 2.50/1.45  tff(c_148, plain, (v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_146])).
% 2.50/1.45  tff(c_22, plain, (![B_13, A_12]: (m1_subset_1(B_13, A_12) | ~v1_xboole_0(B_13) | ~v1_xboole_0(A_12))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.50/1.45  tff(c_32, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.50/1.45  tff(c_253, plain, (![C_62, A_63, B_64]: (r2_hidden(C_62, A_63) | ~r2_hidden(C_62, B_64) | ~m1_subset_1(B_64, k1_zfmisc_1(A_63)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.50/1.45  tff(c_302, plain, (![C_70, A_71]: (r2_hidden(C_70, A_71) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_71)) | ~m1_subset_1(C_70, '#skF_3'))), inference(resolution, [status(thm)], [c_30, c_253])).
% 2.50/1.45  tff(c_310, plain, (![C_72]: (r2_hidden(C_72, '#skF_3') | ~m1_subset_1(C_72, '#skF_3'))), inference(resolution, [status(thm)], [c_32, c_302])).
% 2.50/1.45  tff(c_324, plain, (![C_72]: (~v1_xboole_0('#skF_3') | ~m1_subset_1(C_72, '#skF_3'))), inference(resolution, [status(thm)], [c_310, c_2])).
% 2.50/1.45  tff(c_333, plain, (![C_73]: (~m1_subset_1(C_73, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_148, c_324])).
% 2.50/1.45  tff(c_341, plain, (![B_13]: (~v1_xboole_0(B_13) | ~v1_xboole_0('#skF_3'))), inference(resolution, [status(thm)], [c_22, c_333])).
% 2.50/1.45  tff(c_346, plain, (![B_13]: (~v1_xboole_0(B_13))), inference(demodulation, [status(thm), theory('equality')], [c_148, c_341])).
% 2.50/1.45  tff(c_357, plain, $false, inference(negUnitSimplification, [status(thm)], [c_346, c_148])).
% 2.50/1.45  tff(c_359, plain, (~v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_146])).
% 2.50/1.45  tff(c_10, plain, (![A_5, B_6]: (r2_hidden('#skF_2'(A_5, B_6), A_5) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.50/1.45  tff(c_466, plain, (![A_90, B_91]: (m1_subset_1('#skF_2'(A_90, B_91), A_90) | v1_xboole_0(A_90) | r1_tarski(A_90, B_91))), inference(resolution, [status(thm)], [c_10, c_108])).
% 2.50/1.45  tff(c_80, plain, (![A_37, B_38]: (~r2_hidden('#skF_2'(A_37, B_38), B_38) | r1_tarski(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.50/1.45  tff(c_96, plain, (![A_37]: (r1_tarski(A_37, '#skF_4') | ~m1_subset_1('#skF_2'(A_37, '#skF_4'), '#skF_3'))), inference(resolution, [status(thm)], [c_30, c_80])).
% 2.50/1.45  tff(c_478, plain, (v1_xboole_0('#skF_3') | r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_466, c_96])).
% 2.50/1.45  tff(c_489, plain, (r1_tarski('#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_359, c_478])).
% 2.50/1.45  tff(c_12, plain, (![B_11, A_10]: (B_11=A_10 | ~r1_tarski(B_11, A_10) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.50/1.45  tff(c_498, plain, ('#skF_3'='#skF_4' | ~r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_489, c_12])).
% 2.50/1.45  tff(c_505, plain, (~r1_tarski('#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_28, c_498])).
% 2.50/1.45  tff(c_441, plain, (![C_85, A_86, B_87]: (r2_hidden(C_85, A_86) | ~r2_hidden(C_85, B_87) | ~m1_subset_1(B_87, k1_zfmisc_1(A_86)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.50/1.45  tff(c_707, plain, (![A_117, B_118, A_119]: (r2_hidden('#skF_2'(A_117, B_118), A_119) | ~m1_subset_1(A_117, k1_zfmisc_1(A_119)) | r1_tarski(A_117, B_118))), inference(resolution, [status(thm)], [c_10, c_441])).
% 2.50/1.45  tff(c_8, plain, (![A_5, B_6]: (~r2_hidden('#skF_2'(A_5, B_6), B_6) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.50/1.45  tff(c_727, plain, (![A_120, A_121]: (~m1_subset_1(A_120, k1_zfmisc_1(A_121)) | r1_tarski(A_120, A_121))), inference(resolution, [status(thm)], [c_707, c_8])).
% 2.50/1.45  tff(c_742, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_32, c_727])).
% 2.50/1.45  tff(c_749, plain, $false, inference(negUnitSimplification, [status(thm)], [c_505, c_742])).
% 2.50/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.50/1.45  
% 2.50/1.45  Inference rules
% 2.50/1.45  ----------------------
% 2.50/1.45  #Ref     : 0
% 2.50/1.45  #Sup     : 147
% 2.50/1.45  #Fact    : 0
% 2.50/1.45  #Define  : 0
% 2.50/1.45  #Split   : 5
% 2.50/1.45  #Chain   : 0
% 2.50/1.45  #Close   : 0
% 2.50/1.45  
% 2.50/1.45  Ordering : KBO
% 2.50/1.45  
% 2.50/1.45  Simplification rules
% 2.50/1.45  ----------------------
% 2.50/1.45  #Subsume      : 76
% 2.50/1.45  #Demod        : 15
% 2.50/1.45  #Tautology    : 26
% 2.50/1.45  #SimpNegUnit  : 33
% 2.50/1.45  #BackRed      : 13
% 2.50/1.45  
% 2.50/1.45  #Partial instantiations: 0
% 2.50/1.45  #Strategies tried      : 1
% 2.50/1.45  
% 2.50/1.45  Timing (in seconds)
% 2.50/1.45  ----------------------
% 2.50/1.45  Preprocessing        : 0.32
% 2.50/1.45  Parsing              : 0.16
% 2.50/1.45  CNF conversion       : 0.02
% 2.50/1.45  Main loop            : 0.33
% 2.50/1.45  Inferencing          : 0.13
% 2.50/1.45  Reduction            : 0.08
% 2.50/1.45  Demodulation         : 0.05
% 2.50/1.45  BG Simplification    : 0.02
% 2.50/1.45  Subsumption          : 0.08
% 2.50/1.45  Abstraction          : 0.02
% 2.50/1.45  MUC search           : 0.00
% 2.50/1.45  Cooper               : 0.00
% 2.50/1.45  Total                : 0.68
% 2.50/1.45  Index Insertion      : 0.00
% 2.50/1.45  Index Deletion       : 0.00
% 2.50/1.45  Index Matching       : 0.00
% 2.50/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
