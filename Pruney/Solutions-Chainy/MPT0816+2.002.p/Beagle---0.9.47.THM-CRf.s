%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:55 EST 2020

% Result     : Theorem 3.91s
% Output     : CNFRefutation 3.91s
% Verified   : 
% Statistics : Number of formulae       :   52 (  83 expanded)
%              Number of leaves         :   20 (  38 expanded)
%              Depth                    :   16
%              Number of atoms          :   89 ( 180 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_42,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_55,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( ( r1_tarski(k1_relat_1(C),A)
            & r1_tarski(k2_relat_1(C),B) )
         => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_46,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => ( r1_tarski(k2_zfmisc_1(A,C),k2_zfmisc_1(B,C))
        & r1_tarski(k2_zfmisc_1(C,A),k2_zfmisc_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_zfmisc_1)).

tff(c_25,plain,(
    ! [A_12,B_13] :
      ( m1_subset_1(A_12,k1_zfmisc_1(B_13))
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_18,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_29,plain,(
    ~ r1_tarski('#skF_4',k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_25,c_18])).

tff(c_22,plain,(
    r1_tarski(k1_relat_1('#skF_4'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_24,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_36,plain,(
    ! [A_18,B_19] :
      ( ~ r2_hidden('#skF_1'(A_18,B_19),B_19)
      | r1_tarski(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_41,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_36])).

tff(c_16,plain,(
    ! [A_11] :
      ( r1_tarski(A_11,k2_zfmisc_1(k1_relat_1(A_11),k2_relat_1(A_11)))
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_20,plain,(
    r1_tarski(k2_relat_1('#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_8,plain,(
    ! [C_8,A_6,B_7] :
      ( r1_tarski(k2_zfmisc_1(C_8,A_6),k2_zfmisc_1(C_8,B_7))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_42,plain,(
    ! [C_20,B_21,A_22] :
      ( r2_hidden(C_20,B_21)
      | ~ r2_hidden(C_20,A_22)
      | ~ r1_tarski(A_22,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_50,plain,(
    ! [A_31,B_32,B_33] :
      ( r2_hidden('#skF_1'(A_31,B_32),B_33)
      | ~ r1_tarski(A_31,B_33)
      | r1_tarski(A_31,B_32) ) ),
    inference(resolution,[status(thm)],[c_6,c_42])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_59,plain,(
    ! [A_34,B_35,B_36,B_37] :
      ( r2_hidden('#skF_1'(A_34,B_35),B_36)
      | ~ r1_tarski(B_37,B_36)
      | ~ r1_tarski(A_34,B_37)
      | r1_tarski(A_34,B_35) ) ),
    inference(resolution,[status(thm)],[c_50,c_2])).

tff(c_313,plain,(
    ! [A_85,B_88,A_89,C_87,B_86] :
      ( r2_hidden('#skF_1'(A_85,B_86),k2_zfmisc_1(C_87,B_88))
      | ~ r1_tarski(A_85,k2_zfmisc_1(C_87,A_89))
      | r1_tarski(A_85,B_86)
      | ~ r1_tarski(A_89,B_88) ) ),
    inference(resolution,[status(thm)],[c_8,c_59])).

tff(c_546,plain,(
    ! [B_129,A_133,B_132,C_130,B_131] :
      ( r2_hidden('#skF_1'(k2_zfmisc_1(C_130,A_133),B_129),k2_zfmisc_1(C_130,B_131))
      | r1_tarski(k2_zfmisc_1(C_130,A_133),B_129)
      | ~ r1_tarski(B_132,B_131)
      | ~ r1_tarski(A_133,B_132) ) ),
    inference(resolution,[status(thm)],[c_8,c_313])).

tff(c_590,plain,(
    ! [C_135,A_136,B_137] :
      ( r2_hidden('#skF_1'(k2_zfmisc_1(C_135,A_136),B_137),k2_zfmisc_1(C_135,'#skF_3'))
      | r1_tarski(k2_zfmisc_1(C_135,A_136),B_137)
      | ~ r1_tarski(A_136,k2_relat_1('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_20,c_546])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_599,plain,(
    ! [C_138,A_139] :
      ( r1_tarski(k2_zfmisc_1(C_138,A_139),k2_zfmisc_1(C_138,'#skF_3'))
      | ~ r1_tarski(A_139,k2_relat_1('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_590,c_4])).

tff(c_57,plain,(
    ! [A_31,B_32,B_2,B_33] :
      ( r2_hidden('#skF_1'(A_31,B_32),B_2)
      | ~ r1_tarski(B_33,B_2)
      | ~ r1_tarski(A_31,B_33)
      | r1_tarski(A_31,B_32) ) ),
    inference(resolution,[status(thm)],[c_50,c_2])).

tff(c_658,plain,(
    ! [A_145,B_146,C_147,A_148] :
      ( r2_hidden('#skF_1'(A_145,B_146),k2_zfmisc_1(C_147,'#skF_3'))
      | ~ r1_tarski(A_145,k2_zfmisc_1(C_147,A_148))
      | r1_tarski(A_145,B_146)
      | ~ r1_tarski(A_148,k2_relat_1('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_599,c_57])).

tff(c_702,plain,(
    ! [A_149,B_150] :
      ( r2_hidden('#skF_1'(A_149,B_150),k2_zfmisc_1(k1_relat_1(A_149),'#skF_3'))
      | r1_tarski(A_149,B_150)
      | ~ r1_tarski(k2_relat_1(A_149),k2_relat_1('#skF_4'))
      | ~ v1_relat_1(A_149) ) ),
    inference(resolution,[status(thm)],[c_16,c_658])).

tff(c_711,plain,(
    ! [A_151] :
      ( r1_tarski(A_151,k2_zfmisc_1(k1_relat_1(A_151),'#skF_3'))
      | ~ r1_tarski(k2_relat_1(A_151),k2_relat_1('#skF_4'))
      | ~ v1_relat_1(A_151) ) ),
    inference(resolution,[status(thm)],[c_702,c_4])).

tff(c_714,plain,
    ( r1_tarski('#skF_4',k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_3'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_41,c_711])).

tff(c_717,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_714])).

tff(c_10,plain,(
    ! [A_6,C_8,B_7] :
      ( r1_tarski(k2_zfmisc_1(A_6,C_8),k2_zfmisc_1(B_7,C_8))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_72,plain,(
    ! [B_7,C_8,A_34,B_35,A_6] :
      ( r2_hidden('#skF_1'(A_34,B_35),k2_zfmisc_1(B_7,C_8))
      | ~ r1_tarski(A_34,k2_zfmisc_1(A_6,C_8))
      | r1_tarski(A_34,B_35)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(resolution,[status(thm)],[c_10,c_59])).

tff(c_1190,plain,(
    ! [B_188,B_189] :
      ( r2_hidden('#skF_1'('#skF_4',B_188),k2_zfmisc_1(B_189,'#skF_3'))
      | r1_tarski('#skF_4',B_188)
      | ~ r1_tarski(k1_relat_1('#skF_4'),B_189) ) ),
    inference(resolution,[status(thm)],[c_717,c_72])).

tff(c_1199,plain,(
    ! [B_190] :
      ( r1_tarski('#skF_4',k2_zfmisc_1(B_190,'#skF_3'))
      | ~ r1_tarski(k1_relat_1('#skF_4'),B_190) ) ),
    inference(resolution,[status(thm)],[c_1190,c_4])).

tff(c_1234,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_22,c_1199])).

tff(c_1249,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_29,c_1234])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:14:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.91/1.66  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.91/1.67  
% 3.91/1.67  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.91/1.67  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.91/1.67  
% 3.91/1.67  %Foreground sorts:
% 3.91/1.67  
% 3.91/1.67  
% 3.91/1.67  %Background operators:
% 3.91/1.67  
% 3.91/1.67  
% 3.91/1.67  %Foreground operators:
% 3.91/1.67  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.91/1.67  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.91/1.67  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.91/1.67  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.91/1.67  tff('#skF_2', type, '#skF_2': $i).
% 3.91/1.67  tff('#skF_3', type, '#skF_3': $i).
% 3.91/1.67  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.91/1.67  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.91/1.67  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.91/1.67  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.91/1.67  tff('#skF_4', type, '#skF_4': $i).
% 3.91/1.67  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.91/1.67  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.91/1.67  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.91/1.67  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.91/1.67  
% 3.91/1.69  tff(f_42, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.91/1.69  tff(f_55, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_relset_1)).
% 3.91/1.69  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.91/1.69  tff(f_46, axiom, (![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_relat_1)).
% 3.91/1.69  tff(f_38, axiom, (![A, B, C]: (r1_tarski(A, B) => (r1_tarski(k2_zfmisc_1(A, C), k2_zfmisc_1(B, C)) & r1_tarski(k2_zfmisc_1(C, A), k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t118_zfmisc_1)).
% 3.91/1.69  tff(c_25, plain, (![A_12, B_13]: (m1_subset_1(A_12, k1_zfmisc_1(B_13)) | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.91/1.69  tff(c_18, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.91/1.69  tff(c_29, plain, (~r1_tarski('#skF_4', k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_25, c_18])).
% 3.91/1.69  tff(c_22, plain, (r1_tarski(k1_relat_1('#skF_4'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.91/1.69  tff(c_24, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.91/1.69  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.91/1.69  tff(c_36, plain, (![A_18, B_19]: (~r2_hidden('#skF_1'(A_18, B_19), B_19) | r1_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.91/1.69  tff(c_41, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_36])).
% 3.91/1.69  tff(c_16, plain, (![A_11]: (r1_tarski(A_11, k2_zfmisc_1(k1_relat_1(A_11), k2_relat_1(A_11))) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.91/1.69  tff(c_20, plain, (r1_tarski(k2_relat_1('#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.91/1.69  tff(c_8, plain, (![C_8, A_6, B_7]: (r1_tarski(k2_zfmisc_1(C_8, A_6), k2_zfmisc_1(C_8, B_7)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.91/1.69  tff(c_42, plain, (![C_20, B_21, A_22]: (r2_hidden(C_20, B_21) | ~r2_hidden(C_20, A_22) | ~r1_tarski(A_22, B_21))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.91/1.69  tff(c_50, plain, (![A_31, B_32, B_33]: (r2_hidden('#skF_1'(A_31, B_32), B_33) | ~r1_tarski(A_31, B_33) | r1_tarski(A_31, B_32))), inference(resolution, [status(thm)], [c_6, c_42])).
% 3.91/1.69  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.91/1.69  tff(c_59, plain, (![A_34, B_35, B_36, B_37]: (r2_hidden('#skF_1'(A_34, B_35), B_36) | ~r1_tarski(B_37, B_36) | ~r1_tarski(A_34, B_37) | r1_tarski(A_34, B_35))), inference(resolution, [status(thm)], [c_50, c_2])).
% 3.91/1.69  tff(c_313, plain, (![A_85, B_88, A_89, C_87, B_86]: (r2_hidden('#skF_1'(A_85, B_86), k2_zfmisc_1(C_87, B_88)) | ~r1_tarski(A_85, k2_zfmisc_1(C_87, A_89)) | r1_tarski(A_85, B_86) | ~r1_tarski(A_89, B_88))), inference(resolution, [status(thm)], [c_8, c_59])).
% 3.91/1.69  tff(c_546, plain, (![B_129, A_133, B_132, C_130, B_131]: (r2_hidden('#skF_1'(k2_zfmisc_1(C_130, A_133), B_129), k2_zfmisc_1(C_130, B_131)) | r1_tarski(k2_zfmisc_1(C_130, A_133), B_129) | ~r1_tarski(B_132, B_131) | ~r1_tarski(A_133, B_132))), inference(resolution, [status(thm)], [c_8, c_313])).
% 3.91/1.69  tff(c_590, plain, (![C_135, A_136, B_137]: (r2_hidden('#skF_1'(k2_zfmisc_1(C_135, A_136), B_137), k2_zfmisc_1(C_135, '#skF_3')) | r1_tarski(k2_zfmisc_1(C_135, A_136), B_137) | ~r1_tarski(A_136, k2_relat_1('#skF_4')))), inference(resolution, [status(thm)], [c_20, c_546])).
% 3.91/1.69  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.91/1.69  tff(c_599, plain, (![C_138, A_139]: (r1_tarski(k2_zfmisc_1(C_138, A_139), k2_zfmisc_1(C_138, '#skF_3')) | ~r1_tarski(A_139, k2_relat_1('#skF_4')))), inference(resolution, [status(thm)], [c_590, c_4])).
% 3.91/1.69  tff(c_57, plain, (![A_31, B_32, B_2, B_33]: (r2_hidden('#skF_1'(A_31, B_32), B_2) | ~r1_tarski(B_33, B_2) | ~r1_tarski(A_31, B_33) | r1_tarski(A_31, B_32))), inference(resolution, [status(thm)], [c_50, c_2])).
% 3.91/1.69  tff(c_658, plain, (![A_145, B_146, C_147, A_148]: (r2_hidden('#skF_1'(A_145, B_146), k2_zfmisc_1(C_147, '#skF_3')) | ~r1_tarski(A_145, k2_zfmisc_1(C_147, A_148)) | r1_tarski(A_145, B_146) | ~r1_tarski(A_148, k2_relat_1('#skF_4')))), inference(resolution, [status(thm)], [c_599, c_57])).
% 3.91/1.69  tff(c_702, plain, (![A_149, B_150]: (r2_hidden('#skF_1'(A_149, B_150), k2_zfmisc_1(k1_relat_1(A_149), '#skF_3')) | r1_tarski(A_149, B_150) | ~r1_tarski(k2_relat_1(A_149), k2_relat_1('#skF_4')) | ~v1_relat_1(A_149))), inference(resolution, [status(thm)], [c_16, c_658])).
% 3.91/1.69  tff(c_711, plain, (![A_151]: (r1_tarski(A_151, k2_zfmisc_1(k1_relat_1(A_151), '#skF_3')) | ~r1_tarski(k2_relat_1(A_151), k2_relat_1('#skF_4')) | ~v1_relat_1(A_151))), inference(resolution, [status(thm)], [c_702, c_4])).
% 3.91/1.69  tff(c_714, plain, (r1_tarski('#skF_4', k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_3')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_41, c_711])).
% 3.91/1.69  tff(c_717, plain, (r1_tarski('#skF_4', k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_714])).
% 3.91/1.69  tff(c_10, plain, (![A_6, C_8, B_7]: (r1_tarski(k2_zfmisc_1(A_6, C_8), k2_zfmisc_1(B_7, C_8)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.91/1.69  tff(c_72, plain, (![B_7, C_8, A_34, B_35, A_6]: (r2_hidden('#skF_1'(A_34, B_35), k2_zfmisc_1(B_7, C_8)) | ~r1_tarski(A_34, k2_zfmisc_1(A_6, C_8)) | r1_tarski(A_34, B_35) | ~r1_tarski(A_6, B_7))), inference(resolution, [status(thm)], [c_10, c_59])).
% 3.91/1.69  tff(c_1190, plain, (![B_188, B_189]: (r2_hidden('#skF_1'('#skF_4', B_188), k2_zfmisc_1(B_189, '#skF_3')) | r1_tarski('#skF_4', B_188) | ~r1_tarski(k1_relat_1('#skF_4'), B_189))), inference(resolution, [status(thm)], [c_717, c_72])).
% 3.91/1.69  tff(c_1199, plain, (![B_190]: (r1_tarski('#skF_4', k2_zfmisc_1(B_190, '#skF_3')) | ~r1_tarski(k1_relat_1('#skF_4'), B_190))), inference(resolution, [status(thm)], [c_1190, c_4])).
% 3.91/1.69  tff(c_1234, plain, (r1_tarski('#skF_4', k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_22, c_1199])).
% 3.91/1.69  tff(c_1249, plain, $false, inference(negUnitSimplification, [status(thm)], [c_29, c_1234])).
% 3.91/1.69  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.91/1.69  
% 3.91/1.69  Inference rules
% 3.91/1.69  ----------------------
% 3.91/1.69  #Ref     : 0
% 3.91/1.69  #Sup     : 332
% 3.91/1.69  #Fact    : 0
% 3.91/1.69  #Define  : 0
% 3.91/1.69  #Split   : 6
% 3.91/1.69  #Chain   : 0
% 3.91/1.69  #Close   : 0
% 3.91/1.69  
% 3.91/1.69  Ordering : KBO
% 3.91/1.69  
% 3.91/1.69  Simplification rules
% 3.91/1.69  ----------------------
% 3.91/1.69  #Subsume      : 42
% 3.91/1.69  #Demod        : 5
% 3.91/1.69  #Tautology    : 5
% 3.91/1.69  #SimpNegUnit  : 1
% 3.91/1.69  #BackRed      : 0
% 3.91/1.69  
% 3.91/1.69  #Partial instantiations: 0
% 3.91/1.69  #Strategies tried      : 1
% 3.91/1.69  
% 3.91/1.69  Timing (in seconds)
% 3.91/1.69  ----------------------
% 3.91/1.69  Preprocessing        : 0.27
% 3.91/1.69  Parsing              : 0.16
% 3.91/1.69  CNF conversion       : 0.02
% 3.91/1.69  Main loop            : 0.65
% 3.91/1.69  Inferencing          : 0.20
% 3.91/1.69  Reduction            : 0.14
% 3.91/1.69  Demodulation         : 0.08
% 3.91/1.69  BG Simplification    : 0.02
% 3.91/1.69  Subsumption          : 0.24
% 3.91/1.69  Abstraction          : 0.03
% 3.91/1.69  MUC search           : 0.00
% 3.91/1.69  Cooper               : 0.00
% 3.91/1.69  Total                : 0.94
% 3.91/1.69  Index Insertion      : 0.00
% 3.91/1.69  Index Deletion       : 0.00
% 3.91/1.69  Index Matching       : 0.00
% 3.91/1.69  BG Taut test         : 0.00
%------------------------------------------------------------------------------
