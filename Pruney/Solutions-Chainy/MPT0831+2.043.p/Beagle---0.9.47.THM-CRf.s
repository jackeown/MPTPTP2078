%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:38 EST 2020

% Result     : Theorem 2.44s
% Output     : CNFRefutation 2.69s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 100 expanded)
%              Number of leaves         :   33 (  47 expanded)
%              Depth                    :   13
%              Number of atoms          :  108 ( 176 expanded)
%              Number of equality atoms :    8 (   8 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k5_relset_1,type,(
    k5_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_93,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A)))
       => ( r1_tarski(B,C)
         => r2_relset_1(B,A,k5_relset_1(B,A,D,C),D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_relset_1)).

tff(f_64,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_62,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => ( r1_tarski(k2_zfmisc_1(A,C),k2_zfmisc_1(B,C))
        & r1_tarski(k2_zfmisc_1(C,A),k2_zfmisc_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_zfmisc_1)).

tff(f_45,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => r1_tarski(k1_zfmisc_1(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_zfmisc_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_80,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k5_relset_1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

tff(f_86,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(c_36,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_22,plain,(
    ! [A_19,B_20] : v1_relat_1(k2_zfmisc_1(A_19,B_20)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_38,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_53,plain,(
    ! [B_45,A_46] :
      ( v1_relat_1(B_45)
      | ~ m1_subset_1(B_45,k1_zfmisc_1(A_46))
      | ~ v1_relat_1(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_56,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_38,c_53])).

tff(c_59,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_56])).

tff(c_10,plain,(
    ! [A_6,C_8,B_7] :
      ( r1_tarski(k2_zfmisc_1(A_6,C_8),k2_zfmisc_1(B_7,C_8))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_14,plain,(
    ! [A_11] : ~ v1_xboole_0(k1_zfmisc_1(A_11)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_12,plain,(
    ! [A_9,B_10] :
      ( r1_tarski(k1_zfmisc_1(A_9),k1_zfmisc_1(B_10))
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_18,plain,(
    ! [A_14,B_15] :
      ( r2_hidden(A_14,B_15)
      | v1_xboole_0(B_15)
      | ~ m1_subset_1(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_98,plain,(
    ! [C_58,B_59,A_60] :
      ( r2_hidden(C_58,B_59)
      | ~ r2_hidden(C_58,A_60)
      | ~ r1_tarski(A_60,B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_125,plain,(
    ! [A_71,B_72,B_73] :
      ( r2_hidden(A_71,B_72)
      | ~ r1_tarski(B_73,B_72)
      | v1_xboole_0(B_73)
      | ~ m1_subset_1(A_71,B_73) ) ),
    inference(resolution,[status(thm)],[c_18,c_98])).

tff(c_133,plain,(
    ! [A_71,B_10,A_9] :
      ( r2_hidden(A_71,k1_zfmisc_1(B_10))
      | v1_xboole_0(k1_zfmisc_1(A_9))
      | ~ m1_subset_1(A_71,k1_zfmisc_1(A_9))
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(resolution,[status(thm)],[c_12,c_125])).

tff(c_176,plain,(
    ! [A_84,B_85,A_86] :
      ( r2_hidden(A_84,k1_zfmisc_1(B_85))
      | ~ m1_subset_1(A_84,k1_zfmisc_1(A_86))
      | ~ r1_tarski(A_86,B_85) ) ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_133])).

tff(c_184,plain,(
    ! [B_87] :
      ( r2_hidden('#skF_5',k1_zfmisc_1(B_87))
      | ~ r1_tarski(k2_zfmisc_1('#skF_3','#skF_2'),B_87) ) ),
    inference(resolution,[status(thm)],[c_38,c_176])).

tff(c_16,plain,(
    ! [A_12,B_13] :
      ( m1_subset_1(A_12,B_13)
      | ~ r2_hidden(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_192,plain,(
    ! [B_88] :
      ( m1_subset_1('#skF_5',k1_zfmisc_1(B_88))
      | ~ r1_tarski(k2_zfmisc_1('#skF_3','#skF_2'),B_88) ) ),
    inference(resolution,[status(thm)],[c_184,c_16])).

tff(c_217,plain,(
    ! [B_93] :
      ( m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(B_93,'#skF_2')))
      | ~ r1_tarski('#skF_3',B_93) ) ),
    inference(resolution,[status(thm)],[c_10,c_192])).

tff(c_28,plain,(
    ! [C_25,A_23,B_24] :
      ( v4_relat_1(C_25,A_23)
      | ~ m1_subset_1(C_25,k1_zfmisc_1(k2_zfmisc_1(A_23,B_24))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_242,plain,(
    ! [B_94] :
      ( v4_relat_1('#skF_5',B_94)
      | ~ r1_tarski('#skF_3',B_94) ) ),
    inference(resolution,[status(thm)],[c_217,c_28])).

tff(c_24,plain,(
    ! [B_22,A_21] :
      ( k7_relat_1(B_22,A_21) = B_22
      | ~ v4_relat_1(B_22,A_21)
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_245,plain,(
    ! [B_94] :
      ( k7_relat_1('#skF_5',B_94) = '#skF_5'
      | ~ v1_relat_1('#skF_5')
      | ~ r1_tarski('#skF_3',B_94) ) ),
    inference(resolution,[status(thm)],[c_242,c_24])).

tff(c_249,plain,(
    ! [B_95] :
      ( k7_relat_1('#skF_5',B_95) = '#skF_5'
      | ~ r1_tarski('#skF_3',B_95) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_245])).

tff(c_259,plain,(
    k7_relat_1('#skF_5','#skF_4') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_36,c_249])).

tff(c_143,plain,(
    ! [A_74,B_75,C_76,D_77] :
      ( k5_relset_1(A_74,B_75,C_76,D_77) = k7_relat_1(C_76,D_77)
      | ~ m1_subset_1(C_76,k1_zfmisc_1(k2_zfmisc_1(A_74,B_75))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_150,plain,(
    ! [D_77] : k5_relset_1('#skF_3','#skF_2','#skF_5',D_77) = k7_relat_1('#skF_5',D_77) ),
    inference(resolution,[status(thm)],[c_38,c_143])).

tff(c_34,plain,(
    ~ r2_relset_1('#skF_3','#skF_2',k5_relset_1('#skF_3','#skF_2','#skF_5','#skF_4'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_151,plain,(
    ~ r2_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_5','#skF_4'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_150,c_34])).

tff(c_260,plain,(
    ~ r2_relset_1('#skF_3','#skF_2','#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_259,c_151])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_60,plain,(
    ! [A_47,B_48] :
      ( ~ r2_hidden('#skF_1'(A_47,B_48),B_48)
      | r1_tarski(A_47,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_70,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_60])).

tff(c_8,plain,(
    ! [C_8,A_6,B_7] :
      ( r1_tarski(k2_zfmisc_1(C_8,A_6),k2_zfmisc_1(C_8,B_7))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_206,plain,(
    ! [B_7] :
      ( m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_7)))
      | ~ r1_tarski('#skF_2',B_7) ) ),
    inference(resolution,[status(thm)],[c_8,c_192])).

tff(c_209,plain,(
    ! [A_89,B_90,C_91,D_92] :
      ( r2_relset_1(A_89,B_90,C_91,C_91)
      | ~ m1_subset_1(D_92,k1_zfmisc_1(k2_zfmisc_1(A_89,B_90)))
      | ~ m1_subset_1(C_91,k1_zfmisc_1(k2_zfmisc_1(A_89,B_90))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_291,plain,(
    ! [C_98] :
      ( r2_relset_1('#skF_3','#skF_2',C_98,C_98)
      | ~ m1_subset_1(C_98,k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_38,c_209])).

tff(c_294,plain,
    ( r2_relset_1('#skF_3','#skF_2','#skF_5','#skF_5')
    | ~ r1_tarski('#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_206,c_291])).

tff(c_305,plain,(
    r2_relset_1('#skF_3','#skF_2','#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_294])).

tff(c_307,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_260,c_305])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:13:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.44/1.30  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.44/1.30  
% 2.44/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.69/1.31  %$ r2_relset_1 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.69/1.31  
% 2.69/1.31  %Foreground sorts:
% 2.69/1.31  
% 2.69/1.31  
% 2.69/1.31  %Background operators:
% 2.69/1.31  
% 2.69/1.31  
% 2.69/1.31  %Foreground operators:
% 2.69/1.31  tff(k5_relset_1, type, k5_relset_1: ($i * $i * $i * $i) > $i).
% 2.69/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.69/1.31  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 2.69/1.31  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.69/1.31  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.69/1.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.69/1.31  tff('#skF_5', type, '#skF_5': $i).
% 2.69/1.31  tff('#skF_2', type, '#skF_2': $i).
% 2.69/1.31  tff('#skF_3', type, '#skF_3': $i).
% 2.69/1.31  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.69/1.31  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.69/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.69/1.31  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.69/1.31  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.69/1.31  tff('#skF_4', type, '#skF_4': $i).
% 2.69/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.69/1.31  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.69/1.31  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.69/1.31  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.69/1.31  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.69/1.31  
% 2.69/1.32  tff(f_93, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A))) => (r1_tarski(B, C) => r2_relset_1(B, A, k5_relset_1(B, A, D, C), D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_relset_1)).
% 2.69/1.32  tff(f_64, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.69/1.32  tff(f_62, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.69/1.32  tff(f_38, axiom, (![A, B, C]: (r1_tarski(A, B) => (r1_tarski(k2_zfmisc_1(A, C), k2_zfmisc_1(B, C)) & r1_tarski(k2_zfmisc_1(C, A), k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t118_zfmisc_1)).
% 2.69/1.32  tff(f_45, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 2.69/1.32  tff(f_42, axiom, (![A, B]: (r1_tarski(A, B) => r1_tarski(k1_zfmisc_1(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_zfmisc_1)).
% 2.69/1.32  tff(f_55, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 2.69/1.32  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.69/1.32  tff(f_49, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 2.69/1.32  tff(f_76, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.69/1.32  tff(f_70, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 2.69/1.32  tff(f_80, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k5_relset_1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k5_relset_1)).
% 2.69/1.32  tff(f_86, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 2.69/1.32  tff(c_36, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.69/1.32  tff(c_22, plain, (![A_19, B_20]: (v1_relat_1(k2_zfmisc_1(A_19, B_20)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.69/1.32  tff(c_38, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.69/1.32  tff(c_53, plain, (![B_45, A_46]: (v1_relat_1(B_45) | ~m1_subset_1(B_45, k1_zfmisc_1(A_46)) | ~v1_relat_1(A_46))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.69/1.32  tff(c_56, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_38, c_53])).
% 2.69/1.32  tff(c_59, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_56])).
% 2.69/1.32  tff(c_10, plain, (![A_6, C_8, B_7]: (r1_tarski(k2_zfmisc_1(A_6, C_8), k2_zfmisc_1(B_7, C_8)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.69/1.32  tff(c_14, plain, (![A_11]: (~v1_xboole_0(k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.69/1.32  tff(c_12, plain, (![A_9, B_10]: (r1_tarski(k1_zfmisc_1(A_9), k1_zfmisc_1(B_10)) | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.69/1.32  tff(c_18, plain, (![A_14, B_15]: (r2_hidden(A_14, B_15) | v1_xboole_0(B_15) | ~m1_subset_1(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.69/1.32  tff(c_98, plain, (![C_58, B_59, A_60]: (r2_hidden(C_58, B_59) | ~r2_hidden(C_58, A_60) | ~r1_tarski(A_60, B_59))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.69/1.32  tff(c_125, plain, (![A_71, B_72, B_73]: (r2_hidden(A_71, B_72) | ~r1_tarski(B_73, B_72) | v1_xboole_0(B_73) | ~m1_subset_1(A_71, B_73))), inference(resolution, [status(thm)], [c_18, c_98])).
% 2.69/1.32  tff(c_133, plain, (![A_71, B_10, A_9]: (r2_hidden(A_71, k1_zfmisc_1(B_10)) | v1_xboole_0(k1_zfmisc_1(A_9)) | ~m1_subset_1(A_71, k1_zfmisc_1(A_9)) | ~r1_tarski(A_9, B_10))), inference(resolution, [status(thm)], [c_12, c_125])).
% 2.69/1.32  tff(c_176, plain, (![A_84, B_85, A_86]: (r2_hidden(A_84, k1_zfmisc_1(B_85)) | ~m1_subset_1(A_84, k1_zfmisc_1(A_86)) | ~r1_tarski(A_86, B_85))), inference(negUnitSimplification, [status(thm)], [c_14, c_133])).
% 2.69/1.32  tff(c_184, plain, (![B_87]: (r2_hidden('#skF_5', k1_zfmisc_1(B_87)) | ~r1_tarski(k2_zfmisc_1('#skF_3', '#skF_2'), B_87))), inference(resolution, [status(thm)], [c_38, c_176])).
% 2.69/1.32  tff(c_16, plain, (![A_12, B_13]: (m1_subset_1(A_12, B_13) | ~r2_hidden(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.69/1.32  tff(c_192, plain, (![B_88]: (m1_subset_1('#skF_5', k1_zfmisc_1(B_88)) | ~r1_tarski(k2_zfmisc_1('#skF_3', '#skF_2'), B_88))), inference(resolution, [status(thm)], [c_184, c_16])).
% 2.69/1.32  tff(c_217, plain, (![B_93]: (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(B_93, '#skF_2'))) | ~r1_tarski('#skF_3', B_93))), inference(resolution, [status(thm)], [c_10, c_192])).
% 2.69/1.32  tff(c_28, plain, (![C_25, A_23, B_24]: (v4_relat_1(C_25, A_23) | ~m1_subset_1(C_25, k1_zfmisc_1(k2_zfmisc_1(A_23, B_24))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.69/1.32  tff(c_242, plain, (![B_94]: (v4_relat_1('#skF_5', B_94) | ~r1_tarski('#skF_3', B_94))), inference(resolution, [status(thm)], [c_217, c_28])).
% 2.69/1.32  tff(c_24, plain, (![B_22, A_21]: (k7_relat_1(B_22, A_21)=B_22 | ~v4_relat_1(B_22, A_21) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.69/1.32  tff(c_245, plain, (![B_94]: (k7_relat_1('#skF_5', B_94)='#skF_5' | ~v1_relat_1('#skF_5') | ~r1_tarski('#skF_3', B_94))), inference(resolution, [status(thm)], [c_242, c_24])).
% 2.69/1.32  tff(c_249, plain, (![B_95]: (k7_relat_1('#skF_5', B_95)='#skF_5' | ~r1_tarski('#skF_3', B_95))), inference(demodulation, [status(thm), theory('equality')], [c_59, c_245])).
% 2.69/1.32  tff(c_259, plain, (k7_relat_1('#skF_5', '#skF_4')='#skF_5'), inference(resolution, [status(thm)], [c_36, c_249])).
% 2.69/1.32  tff(c_143, plain, (![A_74, B_75, C_76, D_77]: (k5_relset_1(A_74, B_75, C_76, D_77)=k7_relat_1(C_76, D_77) | ~m1_subset_1(C_76, k1_zfmisc_1(k2_zfmisc_1(A_74, B_75))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.69/1.32  tff(c_150, plain, (![D_77]: (k5_relset_1('#skF_3', '#skF_2', '#skF_5', D_77)=k7_relat_1('#skF_5', D_77))), inference(resolution, [status(thm)], [c_38, c_143])).
% 2.69/1.32  tff(c_34, plain, (~r2_relset_1('#skF_3', '#skF_2', k5_relset_1('#skF_3', '#skF_2', '#skF_5', '#skF_4'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.69/1.32  tff(c_151, plain, (~r2_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_5', '#skF_4'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_150, c_34])).
% 2.69/1.32  tff(c_260, plain, (~r2_relset_1('#skF_3', '#skF_2', '#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_259, c_151])).
% 2.69/1.32  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.69/1.32  tff(c_60, plain, (![A_47, B_48]: (~r2_hidden('#skF_1'(A_47, B_48), B_48) | r1_tarski(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.69/1.32  tff(c_70, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_60])).
% 2.69/1.32  tff(c_8, plain, (![C_8, A_6, B_7]: (r1_tarski(k2_zfmisc_1(C_8, A_6), k2_zfmisc_1(C_8, B_7)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.69/1.32  tff(c_206, plain, (![B_7]: (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_7))) | ~r1_tarski('#skF_2', B_7))), inference(resolution, [status(thm)], [c_8, c_192])).
% 2.69/1.32  tff(c_209, plain, (![A_89, B_90, C_91, D_92]: (r2_relset_1(A_89, B_90, C_91, C_91) | ~m1_subset_1(D_92, k1_zfmisc_1(k2_zfmisc_1(A_89, B_90))) | ~m1_subset_1(C_91, k1_zfmisc_1(k2_zfmisc_1(A_89, B_90))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.69/1.32  tff(c_291, plain, (![C_98]: (r2_relset_1('#skF_3', '#skF_2', C_98, C_98) | ~m1_subset_1(C_98, k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))))), inference(resolution, [status(thm)], [c_38, c_209])).
% 2.69/1.32  tff(c_294, plain, (r2_relset_1('#skF_3', '#skF_2', '#skF_5', '#skF_5') | ~r1_tarski('#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_206, c_291])).
% 2.69/1.32  tff(c_305, plain, (r2_relset_1('#skF_3', '#skF_2', '#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_294])).
% 2.69/1.32  tff(c_307, plain, $false, inference(negUnitSimplification, [status(thm)], [c_260, c_305])).
% 2.69/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.69/1.32  
% 2.69/1.32  Inference rules
% 2.69/1.32  ----------------------
% 2.69/1.32  #Ref     : 0
% 2.69/1.32  #Sup     : 58
% 2.69/1.32  #Fact    : 0
% 2.69/1.32  #Define  : 0
% 2.69/1.32  #Split   : 1
% 2.69/1.32  #Chain   : 0
% 2.69/1.32  #Close   : 0
% 2.69/1.32  
% 2.69/1.32  Ordering : KBO
% 2.69/1.32  
% 2.69/1.32  Simplification rules
% 2.69/1.32  ----------------------
% 2.69/1.32  #Subsume      : 1
% 2.69/1.32  #Demod        : 15
% 2.69/1.32  #Tautology    : 15
% 2.69/1.32  #SimpNegUnit  : 2
% 2.69/1.32  #BackRed      : 2
% 2.69/1.32  
% 2.69/1.32  #Partial instantiations: 0
% 2.69/1.32  #Strategies tried      : 1
% 2.69/1.32  
% 2.69/1.32  Timing (in seconds)
% 2.69/1.32  ----------------------
% 2.69/1.33  Preprocessing        : 0.32
% 2.69/1.33  Parsing              : 0.17
% 2.69/1.33  CNF conversion       : 0.02
% 2.69/1.33  Main loop            : 0.24
% 2.69/1.33  Inferencing          : 0.10
% 2.69/1.33  Reduction            : 0.07
% 2.69/1.33  Demodulation         : 0.05
% 2.69/1.33  BG Simplification    : 0.01
% 2.69/1.33  Subsumption          : 0.05
% 2.69/1.33  Abstraction          : 0.01
% 2.69/1.33  MUC search           : 0.00
% 2.69/1.33  Cooper               : 0.00
% 2.69/1.33  Total                : 0.60
% 2.69/1.33  Index Insertion      : 0.00
% 2.69/1.33  Index Deletion       : 0.00
% 2.69/1.33  Index Matching       : 0.00
% 2.69/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
