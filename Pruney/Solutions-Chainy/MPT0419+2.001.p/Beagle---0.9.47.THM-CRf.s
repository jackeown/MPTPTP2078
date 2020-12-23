%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:51 EST 2020

% Result     : Theorem 3.34s
% Output     : CNFRefutation 3.34s
% Verified   : 
% Statistics : Number of formulae       :   52 (  73 expanded)
%              Number of leaves         :   20 (  35 expanded)
%              Depth                    :   13
%              Number of atoms          :   93 ( 154 expanded)
%              Number of equality atoms :    1 (   1 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > k7_setfam_1 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_setfam_1,type,(
    k7_setfam_1: ( $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_62,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A)))
           => ( r1_tarski(k7_setfam_1(A,B),k7_setfam_1(A,C))
             => r1_tarski(B,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_setfam_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_39,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r2_hidden(k3_subset_1(A,C),k7_setfam_1(A,B))
          <=> r2_hidden(C,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_setfam_1)).

tff(c_28,plain,(
    ~ r1_tarski('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_61,plain,(
    ! [A_28,B_29] :
      ( ~ r2_hidden('#skF_1'(A_28,B_29),B_29)
      | r1_tarski(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_70,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_61])).

tff(c_34,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_35,plain,(
    ! [A_18,B_19] :
      ( r1_tarski(A_18,B_19)
      | ~ m1_subset_1(A_18,k1_zfmisc_1(B_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_43,plain,(
    r1_tarski('#skF_5',k1_zfmisc_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_34,c_35])).

tff(c_73,plain,(
    ! [C_31,B_32,A_33] :
      ( r2_hidden(C_31,B_32)
      | ~ r2_hidden(C_31,A_33)
      | ~ r1_tarski(A_33,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_102,plain,(
    ! [A_43,B_44,B_45] :
      ( r2_hidden('#skF_1'(A_43,B_44),B_45)
      | ~ r1_tarski(A_43,B_45)
      | r1_tarski(A_43,B_44) ) ),
    inference(resolution,[status(thm)],[c_6,c_73])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_137,plain,(
    ! [A_55,B_56,B_57,B_58] :
      ( r2_hidden('#skF_1'(A_55,B_56),B_57)
      | ~ r1_tarski(B_58,B_57)
      | ~ r1_tarski(A_55,B_58)
      | r1_tarski(A_55,B_56) ) ),
    inference(resolution,[status(thm)],[c_102,c_2])).

tff(c_159,plain,(
    ! [A_59,B_60] :
      ( r2_hidden('#skF_1'(A_59,B_60),k1_zfmisc_1('#skF_4'))
      | ~ r1_tarski(A_59,'#skF_5')
      | r1_tarski(A_59,B_60) ) ),
    inference(resolution,[status(thm)],[c_43,c_137])).

tff(c_8,plain,(
    ! [C_10,A_6] :
      ( r1_tarski(C_10,A_6)
      | ~ r2_hidden(C_10,k1_zfmisc_1(A_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_171,plain,(
    ! [A_59,B_60] :
      ( r1_tarski('#skF_1'(A_59,B_60),'#skF_4')
      | ~ r1_tarski(A_59,'#skF_5')
      | r1_tarski(A_59,B_60) ) ),
    inference(resolution,[status(thm)],[c_159,c_8])).

tff(c_22,plain,(
    ! [A_11,B_12] :
      ( m1_subset_1(A_11,k1_zfmisc_1(B_12))
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_32,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k1_zfmisc_1('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_30,plain,(
    r1_tarski(k7_setfam_1('#skF_4','#skF_5'),k7_setfam_1('#skF_4','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_172,plain,(
    ! [A_61,C_62,B_63] :
      ( r2_hidden(k3_subset_1(A_61,C_62),k7_setfam_1(A_61,B_63))
      | ~ r2_hidden(C_62,B_63)
      | ~ m1_subset_1(C_62,k1_zfmisc_1(A_61))
      | ~ m1_subset_1(B_63,k1_zfmisc_1(k1_zfmisc_1(A_61))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_946,plain,(
    ! [A_127,C_128,B_129,B_130] :
      ( r2_hidden(k3_subset_1(A_127,C_128),B_129)
      | ~ r1_tarski(k7_setfam_1(A_127,B_130),B_129)
      | ~ r2_hidden(C_128,B_130)
      | ~ m1_subset_1(C_128,k1_zfmisc_1(A_127))
      | ~ m1_subset_1(B_130,k1_zfmisc_1(k1_zfmisc_1(A_127))) ) ),
    inference(resolution,[status(thm)],[c_172,c_2])).

tff(c_963,plain,(
    ! [C_128] :
      ( r2_hidden(k3_subset_1('#skF_4',C_128),k7_setfam_1('#skF_4','#skF_6'))
      | ~ r2_hidden(C_128,'#skF_5')
      | ~ m1_subset_1(C_128,k1_zfmisc_1('#skF_4'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_30,c_946])).

tff(c_973,plain,(
    ! [C_131] :
      ( r2_hidden(k3_subset_1('#skF_4',C_131),k7_setfam_1('#skF_4','#skF_6'))
      | ~ r2_hidden(C_131,'#skF_5')
      | ~ m1_subset_1(C_131,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_963])).

tff(c_26,plain,(
    ! [C_16,B_14,A_13] :
      ( r2_hidden(C_16,B_14)
      | ~ r2_hidden(k3_subset_1(A_13,C_16),k7_setfam_1(A_13,B_14))
      | ~ m1_subset_1(C_16,k1_zfmisc_1(A_13))
      | ~ m1_subset_1(B_14,k1_zfmisc_1(k1_zfmisc_1(A_13))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_976,plain,(
    ! [C_131] :
      ( r2_hidden(C_131,'#skF_6')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k1_zfmisc_1('#skF_4')))
      | ~ r2_hidden(C_131,'#skF_5')
      | ~ m1_subset_1(C_131,k1_zfmisc_1('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_973,c_26])).

tff(c_983,plain,(
    ! [C_132] :
      ( r2_hidden(C_132,'#skF_6')
      | ~ r2_hidden(C_132,'#skF_5')
      | ~ m1_subset_1(C_132,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_976])).

tff(c_989,plain,(
    ! [A_133] :
      ( r2_hidden(A_133,'#skF_6')
      | ~ r2_hidden(A_133,'#skF_5')
      | ~ r1_tarski(A_133,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_22,c_983])).

tff(c_1020,plain,(
    ! [B_134] :
      ( r2_hidden('#skF_1'('#skF_5',B_134),'#skF_6')
      | ~ r1_tarski('#skF_1'('#skF_5',B_134),'#skF_4')
      | r1_tarski('#skF_5',B_134) ) ),
    inference(resolution,[status(thm)],[c_6,c_989])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1026,plain,
    ( ~ r1_tarski('#skF_1'('#skF_5','#skF_6'),'#skF_4')
    | r1_tarski('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_1020,c_4])).

tff(c_1030,plain,(
    ~ r1_tarski('#skF_1'('#skF_5','#skF_6'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_28,c_1026])).

tff(c_1036,plain,
    ( ~ r1_tarski('#skF_5','#skF_5')
    | r1_tarski('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_171,c_1030])).

tff(c_1044,plain,(
    r1_tarski('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_1036])).

tff(c_1046,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_1044])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:48:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.34/1.50  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.34/1.51  
% 3.34/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.34/1.51  %$ r2_hidden > r1_tarski > m1_subset_1 > k7_setfam_1 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2 > #skF_1
% 3.34/1.51  
% 3.34/1.51  %Foreground sorts:
% 3.34/1.51  
% 3.34/1.51  
% 3.34/1.51  %Background operators:
% 3.34/1.51  
% 3.34/1.51  
% 3.34/1.51  %Foreground operators:
% 3.34/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.34/1.51  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.34/1.51  tff(k7_setfam_1, type, k7_setfam_1: ($i * $i) > $i).
% 3.34/1.51  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.34/1.51  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.34/1.51  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.34/1.51  tff('#skF_5', type, '#skF_5': $i).
% 3.34/1.51  tff('#skF_6', type, '#skF_6': $i).
% 3.34/1.51  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.34/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.34/1.51  tff('#skF_4', type, '#skF_4': $i).
% 3.34/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.34/1.51  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.34/1.51  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.34/1.51  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.34/1.51  
% 3.34/1.52  tff(f_62, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => (r1_tarski(k7_setfam_1(A, B), k7_setfam_1(A, C)) => r1_tarski(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_setfam_1)).
% 3.34/1.52  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.34/1.52  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.34/1.52  tff(f_39, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 3.34/1.52  tff(f_52, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r2_hidden(k3_subset_1(A, C), k7_setfam_1(A, B)) <=> r2_hidden(C, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_setfam_1)).
% 3.34/1.52  tff(c_28, plain, (~r1_tarski('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.34/1.52  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.34/1.52  tff(c_61, plain, (![A_28, B_29]: (~r2_hidden('#skF_1'(A_28, B_29), B_29) | r1_tarski(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.34/1.52  tff(c_70, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_61])).
% 3.34/1.52  tff(c_34, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k1_zfmisc_1('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.34/1.52  tff(c_35, plain, (![A_18, B_19]: (r1_tarski(A_18, B_19) | ~m1_subset_1(A_18, k1_zfmisc_1(B_19)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.34/1.52  tff(c_43, plain, (r1_tarski('#skF_5', k1_zfmisc_1('#skF_4'))), inference(resolution, [status(thm)], [c_34, c_35])).
% 3.34/1.52  tff(c_73, plain, (![C_31, B_32, A_33]: (r2_hidden(C_31, B_32) | ~r2_hidden(C_31, A_33) | ~r1_tarski(A_33, B_32))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.34/1.52  tff(c_102, plain, (![A_43, B_44, B_45]: (r2_hidden('#skF_1'(A_43, B_44), B_45) | ~r1_tarski(A_43, B_45) | r1_tarski(A_43, B_44))), inference(resolution, [status(thm)], [c_6, c_73])).
% 3.34/1.52  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.34/1.52  tff(c_137, plain, (![A_55, B_56, B_57, B_58]: (r2_hidden('#skF_1'(A_55, B_56), B_57) | ~r1_tarski(B_58, B_57) | ~r1_tarski(A_55, B_58) | r1_tarski(A_55, B_56))), inference(resolution, [status(thm)], [c_102, c_2])).
% 3.34/1.52  tff(c_159, plain, (![A_59, B_60]: (r2_hidden('#skF_1'(A_59, B_60), k1_zfmisc_1('#skF_4')) | ~r1_tarski(A_59, '#skF_5') | r1_tarski(A_59, B_60))), inference(resolution, [status(thm)], [c_43, c_137])).
% 3.34/1.52  tff(c_8, plain, (![C_10, A_6]: (r1_tarski(C_10, A_6) | ~r2_hidden(C_10, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.34/1.52  tff(c_171, plain, (![A_59, B_60]: (r1_tarski('#skF_1'(A_59, B_60), '#skF_4') | ~r1_tarski(A_59, '#skF_5') | r1_tarski(A_59, B_60))), inference(resolution, [status(thm)], [c_159, c_8])).
% 3.34/1.52  tff(c_22, plain, (![A_11, B_12]: (m1_subset_1(A_11, k1_zfmisc_1(B_12)) | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.34/1.52  tff(c_32, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k1_zfmisc_1('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.34/1.52  tff(c_30, plain, (r1_tarski(k7_setfam_1('#skF_4', '#skF_5'), k7_setfam_1('#skF_4', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.34/1.52  tff(c_172, plain, (![A_61, C_62, B_63]: (r2_hidden(k3_subset_1(A_61, C_62), k7_setfam_1(A_61, B_63)) | ~r2_hidden(C_62, B_63) | ~m1_subset_1(C_62, k1_zfmisc_1(A_61)) | ~m1_subset_1(B_63, k1_zfmisc_1(k1_zfmisc_1(A_61))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.34/1.52  tff(c_946, plain, (![A_127, C_128, B_129, B_130]: (r2_hidden(k3_subset_1(A_127, C_128), B_129) | ~r1_tarski(k7_setfam_1(A_127, B_130), B_129) | ~r2_hidden(C_128, B_130) | ~m1_subset_1(C_128, k1_zfmisc_1(A_127)) | ~m1_subset_1(B_130, k1_zfmisc_1(k1_zfmisc_1(A_127))))), inference(resolution, [status(thm)], [c_172, c_2])).
% 3.34/1.52  tff(c_963, plain, (![C_128]: (r2_hidden(k3_subset_1('#skF_4', C_128), k7_setfam_1('#skF_4', '#skF_6')) | ~r2_hidden(C_128, '#skF_5') | ~m1_subset_1(C_128, k1_zfmisc_1('#skF_4')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k1_zfmisc_1('#skF_4'))))), inference(resolution, [status(thm)], [c_30, c_946])).
% 3.34/1.52  tff(c_973, plain, (![C_131]: (r2_hidden(k3_subset_1('#skF_4', C_131), k7_setfam_1('#skF_4', '#skF_6')) | ~r2_hidden(C_131, '#skF_5') | ~m1_subset_1(C_131, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_963])).
% 3.34/1.52  tff(c_26, plain, (![C_16, B_14, A_13]: (r2_hidden(C_16, B_14) | ~r2_hidden(k3_subset_1(A_13, C_16), k7_setfam_1(A_13, B_14)) | ~m1_subset_1(C_16, k1_zfmisc_1(A_13)) | ~m1_subset_1(B_14, k1_zfmisc_1(k1_zfmisc_1(A_13))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.34/1.52  tff(c_976, plain, (![C_131]: (r2_hidden(C_131, '#skF_6') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k1_zfmisc_1('#skF_4'))) | ~r2_hidden(C_131, '#skF_5') | ~m1_subset_1(C_131, k1_zfmisc_1('#skF_4')))), inference(resolution, [status(thm)], [c_973, c_26])).
% 3.34/1.52  tff(c_983, plain, (![C_132]: (r2_hidden(C_132, '#skF_6') | ~r2_hidden(C_132, '#skF_5') | ~m1_subset_1(C_132, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_976])).
% 3.34/1.52  tff(c_989, plain, (![A_133]: (r2_hidden(A_133, '#skF_6') | ~r2_hidden(A_133, '#skF_5') | ~r1_tarski(A_133, '#skF_4'))), inference(resolution, [status(thm)], [c_22, c_983])).
% 3.34/1.52  tff(c_1020, plain, (![B_134]: (r2_hidden('#skF_1'('#skF_5', B_134), '#skF_6') | ~r1_tarski('#skF_1'('#skF_5', B_134), '#skF_4') | r1_tarski('#skF_5', B_134))), inference(resolution, [status(thm)], [c_6, c_989])).
% 3.34/1.52  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.34/1.52  tff(c_1026, plain, (~r1_tarski('#skF_1'('#skF_5', '#skF_6'), '#skF_4') | r1_tarski('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_1020, c_4])).
% 3.34/1.52  tff(c_1030, plain, (~r1_tarski('#skF_1'('#skF_5', '#skF_6'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_28, c_28, c_1026])).
% 3.34/1.52  tff(c_1036, plain, (~r1_tarski('#skF_5', '#skF_5') | r1_tarski('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_171, c_1030])).
% 3.34/1.52  tff(c_1044, plain, (r1_tarski('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_1036])).
% 3.34/1.52  tff(c_1046, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_1044])).
% 3.34/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.34/1.52  
% 3.34/1.52  Inference rules
% 3.34/1.52  ----------------------
% 3.34/1.52  #Ref     : 0
% 3.34/1.52  #Sup     : 243
% 3.34/1.52  #Fact    : 0
% 3.34/1.52  #Define  : 0
% 3.34/1.52  #Split   : 12
% 3.34/1.52  #Chain   : 0
% 3.34/1.52  #Close   : 0
% 3.34/1.52  
% 3.34/1.52  Ordering : KBO
% 3.34/1.52  
% 3.34/1.52  Simplification rules
% 3.34/1.52  ----------------------
% 3.34/1.52  #Subsume      : 49
% 3.34/1.52  #Demod        : 7
% 3.34/1.52  #Tautology    : 11
% 3.34/1.52  #SimpNegUnit  : 3
% 3.34/1.52  #BackRed      : 0
% 3.34/1.52  
% 3.34/1.52  #Partial instantiations: 0
% 3.34/1.52  #Strategies tried      : 1
% 3.34/1.52  
% 3.34/1.52  Timing (in seconds)
% 3.34/1.52  ----------------------
% 3.34/1.53  Preprocessing        : 0.27
% 3.34/1.53  Parsing              : 0.14
% 3.34/1.53  CNF conversion       : 0.02
% 3.34/1.53  Main loop            : 0.51
% 3.34/1.53  Inferencing          : 0.18
% 3.34/1.53  Reduction            : 0.13
% 3.34/1.53  Demodulation         : 0.08
% 3.34/1.53  BG Simplification    : 0.02
% 3.34/1.53  Subsumption          : 0.15
% 3.34/1.53  Abstraction          : 0.02
% 3.34/1.53  MUC search           : 0.00
% 3.34/1.53  Cooper               : 0.00
% 3.34/1.53  Total                : 0.80
% 3.34/1.53  Index Insertion      : 0.00
% 3.34/1.53  Index Deletion       : 0.00
% 3.34/1.53  Index Matching       : 0.00
% 3.34/1.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
