%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:22 EST 2020

% Result     : Theorem 5.32s
% Output     : CNFRefutation 5.32s
% Verified   : 
% Statistics : Number of formulae       :   55 (  67 expanded)
%              Number of leaves         :   25 (  34 expanded)
%              Depth                    :    9
%              Number of atoms          :   91 ( 127 expanded)
%              Number of equality atoms :   10 (  16 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_86,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(A))
       => ( ( r1_tarski(B,C)
            & r1_tarski(B,k3_subset_1(A,C)) )
         => B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_subset_1)).

tff(f_62,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_tarski(B,C)
          <=> r1_tarski(k3_subset_1(A,C),k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_subset_1)).

tff(f_59,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( r1_tarski(B,k3_subset_1(A,B))
      <=> B = k1_subset_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_subset_1)).

tff(c_44,plain,(
    r1_tarski('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_46,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_30,plain,(
    ! [A_16] : ~ v1_xboole_0(k1_zfmisc_1(A_16)) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_91,plain,(
    ! [B_37,A_38] :
      ( r2_hidden(B_37,A_38)
      | ~ m1_subset_1(B_37,A_38)
      | v1_xboole_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_8,plain,(
    ! [C_12,A_8] :
      ( r1_tarski(C_12,A_8)
      | ~ r2_hidden(C_12,k1_zfmisc_1(A_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_95,plain,(
    ! [B_37,A_8] :
      ( r1_tarski(B_37,A_8)
      | ~ m1_subset_1(B_37,k1_zfmisc_1(A_8))
      | v1_xboole_0(k1_zfmisc_1(A_8)) ) ),
    inference(resolution,[status(thm)],[c_91,c_8])).

tff(c_103,plain,(
    ! [B_39,A_40] :
      ( r1_tarski(B_39,A_40)
      | ~ m1_subset_1(B_39,k1_zfmisc_1(A_40)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_95])).

tff(c_112,plain,(
    r1_tarski('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_103])).

tff(c_149,plain,(
    ! [A_46,C_47,B_48] :
      ( r1_tarski(A_46,C_47)
      | ~ r1_tarski(B_48,C_47)
      | ~ r1_tarski(A_46,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_171,plain,(
    ! [A_50] :
      ( r1_tarski(A_50,'#skF_4')
      | ~ r1_tarski(A_50,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_112,c_149])).

tff(c_184,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_171])).

tff(c_10,plain,(
    ! [C_12,A_8] :
      ( r2_hidden(C_12,k1_zfmisc_1(A_8))
      | ~ r1_tarski(C_12,A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_113,plain,(
    ! [B_41,A_42] :
      ( m1_subset_1(B_41,A_42)
      | ~ r2_hidden(B_41,A_42)
      | v1_xboole_0(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_119,plain,(
    ! [C_12,A_8] :
      ( m1_subset_1(C_12,k1_zfmisc_1(A_8))
      | v1_xboole_0(k1_zfmisc_1(A_8))
      | ~ r1_tarski(C_12,A_8) ) ),
    inference(resolution,[status(thm)],[c_10,c_113])).

tff(c_126,plain,(
    ! [C_12,A_8] :
      ( m1_subset_1(C_12,k1_zfmisc_1(A_8))
      | ~ r1_tarski(C_12,A_8) ) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_119])).

tff(c_40,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_42,plain,(
    r1_tarski('#skF_5',k3_subset_1('#skF_4','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_1059,plain,(
    ! [A_103,C_104,B_105] :
      ( r1_tarski(k3_subset_1(A_103,C_104),k3_subset_1(A_103,B_105))
      | ~ r1_tarski(B_105,C_104)
      | ~ m1_subset_1(C_104,k1_zfmisc_1(A_103))
      | ~ m1_subset_1(B_105,k1_zfmisc_1(A_103)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_6,plain,(
    ! [A_5,C_7,B_6] :
      ( r1_tarski(A_5,C_7)
      | ~ r1_tarski(B_6,C_7)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_3106,plain,(
    ! [A_169,A_170,B_171,C_172] :
      ( r1_tarski(A_169,k3_subset_1(A_170,B_171))
      | ~ r1_tarski(A_169,k3_subset_1(A_170,C_172))
      | ~ r1_tarski(B_171,C_172)
      | ~ m1_subset_1(C_172,k1_zfmisc_1(A_170))
      | ~ m1_subset_1(B_171,k1_zfmisc_1(A_170)) ) ),
    inference(resolution,[status(thm)],[c_1059,c_6])).

tff(c_3165,plain,(
    ! [B_171] :
      ( r1_tarski('#skF_5',k3_subset_1('#skF_4',B_171))
      | ~ r1_tarski(B_171,'#skF_6')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1('#skF_4'))
      | ~ m1_subset_1(B_171,k1_zfmisc_1('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_42,c_3106])).

tff(c_3352,plain,(
    ! [B_175] :
      ( r1_tarski('#skF_5',k3_subset_1('#skF_4',B_175))
      | ~ r1_tarski(B_175,'#skF_6')
      | ~ m1_subset_1(B_175,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_3165])).

tff(c_28,plain,(
    ! [A_15] : k1_subset_1(A_15) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_38,plain,(
    ! [A_21,B_22] :
      ( k1_subset_1(A_21) = B_22
      | ~ r1_tarski(B_22,k3_subset_1(A_21,B_22))
      | ~ m1_subset_1(B_22,k1_zfmisc_1(A_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_47,plain,(
    ! [B_22,A_21] :
      ( k1_xboole_0 = B_22
      | ~ r1_tarski(B_22,k3_subset_1(A_21,B_22))
      | ~ m1_subset_1(B_22,k1_zfmisc_1(A_21)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_38])).

tff(c_3360,plain,
    ( k1_xboole_0 = '#skF_5'
    | ~ r1_tarski('#skF_5','#skF_6')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_3352,c_47])).

tff(c_3370,plain,
    ( k1_xboole_0 = '#skF_5'
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_3360])).

tff(c_3371,plain,(
    ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_3370])).

tff(c_3377,plain,(
    ~ r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_126,c_3371])).

tff(c_3384,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_184,c_3377])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n001.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:45:14 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.32/2.02  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.32/2.03  
% 5.32/2.03  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.32/2.03  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2
% 5.32/2.03  
% 5.32/2.03  %Foreground sorts:
% 5.32/2.03  
% 5.32/2.03  
% 5.32/2.03  %Background operators:
% 5.32/2.03  
% 5.32/2.03  
% 5.32/2.03  %Foreground operators:
% 5.32/2.03  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.32/2.03  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.32/2.03  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.32/2.03  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.32/2.03  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 5.32/2.03  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.32/2.03  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 5.32/2.03  tff('#skF_5', type, '#skF_5': $i).
% 5.32/2.03  tff('#skF_6', type, '#skF_6': $i).
% 5.32/2.03  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.32/2.03  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.32/2.03  tff('#skF_4', type, '#skF_4': $i).
% 5.32/2.03  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.32/2.03  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.32/2.03  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 5.32/2.03  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.32/2.03  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.32/2.03  
% 5.32/2.04  tff(f_86, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((r1_tarski(B, C) & r1_tarski(B, k3_subset_1(A, C))) => (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_subset_1)).
% 5.32/2.04  tff(f_62, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 5.32/2.04  tff(f_57, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 5.32/2.04  tff(f_44, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 5.32/2.04  tff(f_37, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 5.32/2.04  tff(f_71, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, C) <=> r1_tarski(k3_subset_1(A, C), k3_subset_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_subset_1)).
% 5.32/2.04  tff(f_59, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_subset_1)).
% 5.32/2.04  tff(f_77, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(B, k3_subset_1(A, B)) <=> (B = k1_subset_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_subset_1)).
% 5.32/2.04  tff(c_44, plain, (r1_tarski('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_86])).
% 5.32/2.04  tff(c_46, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_86])).
% 5.32/2.04  tff(c_30, plain, (![A_16]: (~v1_xboole_0(k1_zfmisc_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.32/2.04  tff(c_91, plain, (![B_37, A_38]: (r2_hidden(B_37, A_38) | ~m1_subset_1(B_37, A_38) | v1_xboole_0(A_38))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.32/2.04  tff(c_8, plain, (![C_12, A_8]: (r1_tarski(C_12, A_8) | ~r2_hidden(C_12, k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.32/2.04  tff(c_95, plain, (![B_37, A_8]: (r1_tarski(B_37, A_8) | ~m1_subset_1(B_37, k1_zfmisc_1(A_8)) | v1_xboole_0(k1_zfmisc_1(A_8)))), inference(resolution, [status(thm)], [c_91, c_8])).
% 5.32/2.04  tff(c_103, plain, (![B_39, A_40]: (r1_tarski(B_39, A_40) | ~m1_subset_1(B_39, k1_zfmisc_1(A_40)))), inference(negUnitSimplification, [status(thm)], [c_30, c_95])).
% 5.32/2.04  tff(c_112, plain, (r1_tarski('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_46, c_103])).
% 5.32/2.04  tff(c_149, plain, (![A_46, C_47, B_48]: (r1_tarski(A_46, C_47) | ~r1_tarski(B_48, C_47) | ~r1_tarski(A_46, B_48))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.32/2.04  tff(c_171, plain, (![A_50]: (r1_tarski(A_50, '#skF_4') | ~r1_tarski(A_50, '#skF_6'))), inference(resolution, [status(thm)], [c_112, c_149])).
% 5.32/2.04  tff(c_184, plain, (r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_44, c_171])).
% 5.32/2.04  tff(c_10, plain, (![C_12, A_8]: (r2_hidden(C_12, k1_zfmisc_1(A_8)) | ~r1_tarski(C_12, A_8))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.32/2.04  tff(c_113, plain, (![B_41, A_42]: (m1_subset_1(B_41, A_42) | ~r2_hidden(B_41, A_42) | v1_xboole_0(A_42))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.32/2.04  tff(c_119, plain, (![C_12, A_8]: (m1_subset_1(C_12, k1_zfmisc_1(A_8)) | v1_xboole_0(k1_zfmisc_1(A_8)) | ~r1_tarski(C_12, A_8))), inference(resolution, [status(thm)], [c_10, c_113])).
% 5.32/2.04  tff(c_126, plain, (![C_12, A_8]: (m1_subset_1(C_12, k1_zfmisc_1(A_8)) | ~r1_tarski(C_12, A_8))), inference(negUnitSimplification, [status(thm)], [c_30, c_119])).
% 5.32/2.04  tff(c_40, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_86])).
% 5.32/2.04  tff(c_42, plain, (r1_tarski('#skF_5', k3_subset_1('#skF_4', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_86])).
% 5.32/2.04  tff(c_1059, plain, (![A_103, C_104, B_105]: (r1_tarski(k3_subset_1(A_103, C_104), k3_subset_1(A_103, B_105)) | ~r1_tarski(B_105, C_104) | ~m1_subset_1(C_104, k1_zfmisc_1(A_103)) | ~m1_subset_1(B_105, k1_zfmisc_1(A_103)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 5.32/2.04  tff(c_6, plain, (![A_5, C_7, B_6]: (r1_tarski(A_5, C_7) | ~r1_tarski(B_6, C_7) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.32/2.04  tff(c_3106, plain, (![A_169, A_170, B_171, C_172]: (r1_tarski(A_169, k3_subset_1(A_170, B_171)) | ~r1_tarski(A_169, k3_subset_1(A_170, C_172)) | ~r1_tarski(B_171, C_172) | ~m1_subset_1(C_172, k1_zfmisc_1(A_170)) | ~m1_subset_1(B_171, k1_zfmisc_1(A_170)))), inference(resolution, [status(thm)], [c_1059, c_6])).
% 5.32/2.04  tff(c_3165, plain, (![B_171]: (r1_tarski('#skF_5', k3_subset_1('#skF_4', B_171)) | ~r1_tarski(B_171, '#skF_6') | ~m1_subset_1('#skF_6', k1_zfmisc_1('#skF_4')) | ~m1_subset_1(B_171, k1_zfmisc_1('#skF_4')))), inference(resolution, [status(thm)], [c_42, c_3106])).
% 5.32/2.04  tff(c_3352, plain, (![B_175]: (r1_tarski('#skF_5', k3_subset_1('#skF_4', B_175)) | ~r1_tarski(B_175, '#skF_6') | ~m1_subset_1(B_175, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_3165])).
% 5.32/2.04  tff(c_28, plain, (![A_15]: (k1_subset_1(A_15)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.32/2.04  tff(c_38, plain, (![A_21, B_22]: (k1_subset_1(A_21)=B_22 | ~r1_tarski(B_22, k3_subset_1(A_21, B_22)) | ~m1_subset_1(B_22, k1_zfmisc_1(A_21)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 5.32/2.04  tff(c_47, plain, (![B_22, A_21]: (k1_xboole_0=B_22 | ~r1_tarski(B_22, k3_subset_1(A_21, B_22)) | ~m1_subset_1(B_22, k1_zfmisc_1(A_21)))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_38])).
% 5.32/2.04  tff(c_3360, plain, (k1_xboole_0='#skF_5' | ~r1_tarski('#skF_5', '#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4'))), inference(resolution, [status(thm)], [c_3352, c_47])).
% 5.32/2.04  tff(c_3370, plain, (k1_xboole_0='#skF_5' | ~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_3360])).
% 5.32/2.04  tff(c_3371, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_40, c_3370])).
% 5.32/2.04  tff(c_3377, plain, (~r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_126, c_3371])).
% 5.32/2.04  tff(c_3384, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_184, c_3377])).
% 5.32/2.04  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.32/2.04  
% 5.32/2.04  Inference rules
% 5.32/2.04  ----------------------
% 5.32/2.04  #Ref     : 0
% 5.32/2.04  #Sup     : 715
% 5.32/2.04  #Fact    : 0
% 5.32/2.04  #Define  : 0
% 5.32/2.04  #Split   : 6
% 5.32/2.04  #Chain   : 0
% 5.32/2.04  #Close   : 0
% 5.32/2.04  
% 5.32/2.04  Ordering : KBO
% 5.32/2.04  
% 5.32/2.04  Simplification rules
% 5.32/2.04  ----------------------
% 5.32/2.04  #Subsume      : 107
% 5.32/2.04  #Demod        : 167
% 5.32/2.04  #Tautology    : 103
% 5.32/2.04  #SimpNegUnit  : 20
% 5.32/2.04  #BackRed      : 29
% 5.32/2.04  
% 5.32/2.04  #Partial instantiations: 0
% 5.32/2.04  #Strategies tried      : 1
% 5.32/2.04  
% 5.32/2.04  Timing (in seconds)
% 5.32/2.04  ----------------------
% 5.32/2.04  Preprocessing        : 0.31
% 5.32/2.04  Parsing              : 0.16
% 5.32/2.04  CNF conversion       : 0.02
% 5.32/2.04  Main loop            : 0.98
% 5.32/2.04  Inferencing          : 0.32
% 5.32/2.04  Reduction            : 0.28
% 5.32/2.04  Demodulation         : 0.19
% 5.32/2.04  BG Simplification    : 0.04
% 5.32/2.05  Subsumption          : 0.25
% 5.32/2.05  Abstraction          : 0.05
% 5.32/2.05  MUC search           : 0.00
% 5.32/2.05  Cooper               : 0.00
% 5.32/2.05  Total                : 1.32
% 5.32/2.05  Index Insertion      : 0.00
% 5.32/2.05  Index Deletion       : 0.00
% 5.32/2.05  Index Matching       : 0.00
% 5.32/2.05  BG Taut test         : 0.00
%------------------------------------------------------------------------------
