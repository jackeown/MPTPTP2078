%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:11 EST 2020

% Result     : Theorem 2.57s
% Output     : CNFRefutation 2.88s
% Verified   : 
% Statistics : Number of formulae       :   77 (  89 expanded)
%              Number of leaves         :   41 (  49 expanded)
%              Depth                    :   10
%              Number of atoms          :  105 ( 149 expanded)
%              Number of equality atoms :   36 (  44 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k2_relset_1 > k1_relset_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_111,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_31,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_29,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_46,axiom,(
    ! [A,B] :
      ( k3_xboole_0(A,k1_tarski(B)) = k1_tarski(B)
     => r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l29_zfmisc_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_100,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => ( v1_funct_2(C,A,B)
          <=> A = k1_relset_1(A,B,C) ) )
        & ( B = k1_xboole_0
         => ( A = k1_xboole_0
            | ( v1_funct_2(C,A,B)
            <=> C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => r2_hidden(k1_funct_1(B,A),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_funct_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(c_52,plain,(
    k1_funct_1('#skF_6','#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_54,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_56,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_187,plain,(
    ! [C_52,A_53,B_54] :
      ( v1_relat_1(C_52)
      | ~ m1_subset_1(C_52,k1_zfmisc_1(k2_zfmisc_1(A_53,B_54))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_191,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_56,c_187])).

tff(c_60,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_6,plain,(
    ! [A_4] : r1_tarski(k1_xboole_0,A_4) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_79,plain,(
    ! [B_42,A_43] : k3_xboole_0(B_42,A_43) = k3_xboole_0(A_43,B_42) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_3] : k3_xboole_0(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_95,plain,(
    ! [A_43] : k3_xboole_0(k1_xboole_0,A_43) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_79,c_4])).

tff(c_192,plain,(
    ! [B_55,A_56] :
      ( r2_hidden(B_55,A_56)
      | k3_xboole_0(A_56,k1_tarski(B_55)) != k1_tarski(B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_205,plain,(
    ! [B_57] :
      ( r2_hidden(B_57,k1_xboole_0)
      | k1_tarski(B_57) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_95,c_192])).

tff(c_30,plain,(
    ! [B_22,A_21] :
      ( ~ r1_tarski(B_22,A_21)
      | ~ r2_hidden(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_208,plain,(
    ! [B_57] :
      ( ~ r1_tarski(k1_xboole_0,B_57)
      | k1_tarski(B_57) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_205,c_30])).

tff(c_211,plain,(
    ! [B_57] : k1_tarski(B_57) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_208])).

tff(c_58,plain,(
    v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_260,plain,(
    ! [A_77,B_78,C_79] :
      ( k1_relset_1(A_77,B_78,C_79) = k1_relat_1(C_79)
      | ~ m1_subset_1(C_79,k1_zfmisc_1(k2_zfmisc_1(A_77,B_78))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_264,plain,(
    k1_relset_1('#skF_3',k1_tarski('#skF_4'),'#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_56,c_260])).

tff(c_504,plain,(
    ! [B_126,A_127,C_128] :
      ( k1_xboole_0 = B_126
      | k1_relset_1(A_127,B_126,C_128) = A_127
      | ~ v1_funct_2(C_128,A_127,B_126)
      | ~ m1_subset_1(C_128,k1_zfmisc_1(k2_zfmisc_1(A_127,B_126))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_511,plain,
    ( k1_tarski('#skF_4') = k1_xboole_0
    | k1_relset_1('#skF_3',k1_tarski('#skF_4'),'#skF_6') = '#skF_3'
    | ~ v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_56,c_504])).

tff(c_515,plain,
    ( k1_tarski('#skF_4') = k1_xboole_0
    | k1_relat_1('#skF_6') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_264,c_511])).

tff(c_516,plain,(
    k1_relat_1('#skF_6') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_211,c_515])).

tff(c_251,plain,(
    ! [A_74,B_75,C_76] :
      ( k2_relset_1(A_74,B_75,C_76) = k2_relat_1(C_76)
      | ~ m1_subset_1(C_76,k1_zfmisc_1(k2_zfmisc_1(A_74,B_75))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_255,plain,(
    k2_relset_1('#skF_3',k1_tarski('#skF_4'),'#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_56,c_251])).

tff(c_290,plain,(
    ! [A_83,B_84,C_85] :
      ( m1_subset_1(k2_relset_1(A_83,B_84,C_85),k1_zfmisc_1(B_84))
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k2_zfmisc_1(A_83,B_84))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_305,plain,
    ( m1_subset_1(k2_relat_1('#skF_6'),k1_zfmisc_1(k1_tarski('#skF_4')))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')))) ),
    inference(superposition,[status(thm),theory(equality)],[c_255,c_290])).

tff(c_310,plain,(
    m1_subset_1(k2_relat_1('#skF_6'),k1_zfmisc_1(k1_tarski('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_305])).

tff(c_368,plain,(
    ! [B_95,A_96] :
      ( r2_hidden(k1_funct_1(B_95,A_96),k2_relat_1(B_95))
      | ~ r2_hidden(A_96,k1_relat_1(B_95))
      | ~ v1_funct_1(B_95)
      | ~ v1_relat_1(B_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_26,plain,(
    ! [C_18,A_15,B_16] :
      ( r2_hidden(C_18,A_15)
      | ~ r2_hidden(C_18,B_16)
      | ~ m1_subset_1(B_16,k1_zfmisc_1(A_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_530,plain,(
    ! [B_132,A_133,A_134] :
      ( r2_hidden(k1_funct_1(B_132,A_133),A_134)
      | ~ m1_subset_1(k2_relat_1(B_132),k1_zfmisc_1(A_134))
      | ~ r2_hidden(A_133,k1_relat_1(B_132))
      | ~ v1_funct_1(B_132)
      | ~ v1_relat_1(B_132) ) ),
    inference(resolution,[status(thm)],[c_368,c_26])).

tff(c_532,plain,(
    ! [A_133] :
      ( r2_hidden(k1_funct_1('#skF_6',A_133),k1_tarski('#skF_4'))
      | ~ r2_hidden(A_133,k1_relat_1('#skF_6'))
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_310,c_530])).

tff(c_541,plain,(
    ! [A_139] :
      ( r2_hidden(k1_funct_1('#skF_6',A_139),k1_tarski('#skF_4'))
      | ~ r2_hidden(A_139,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_191,c_60,c_516,c_532])).

tff(c_8,plain,(
    ! [C_9,A_5] :
      ( C_9 = A_5
      | ~ r2_hidden(C_9,k1_tarski(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_553,plain,(
    ! [A_140] :
      ( k1_funct_1('#skF_6',A_140) = '#skF_4'
      | ~ r2_hidden(A_140,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_541,c_8])).

tff(c_568,plain,(
    k1_funct_1('#skF_6','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_54,c_553])).

tff(c_575,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_568])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n003.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 20:10:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.57/1.41  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.57/1.42  
% 2.57/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.88/1.42  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k2_relset_1 > k1_relset_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.88/1.42  
% 2.88/1.42  %Foreground sorts:
% 2.88/1.42  
% 2.88/1.42  
% 2.88/1.42  %Background operators:
% 2.88/1.42  
% 2.88/1.42  
% 2.88/1.42  %Foreground operators:
% 2.88/1.42  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.88/1.42  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.88/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.88/1.42  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.88/1.42  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.88/1.42  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.88/1.42  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.88/1.42  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.88/1.42  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.88/1.42  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.88/1.42  tff('#skF_5', type, '#skF_5': $i).
% 2.88/1.42  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.88/1.42  tff('#skF_6', type, '#skF_6': $i).
% 2.88/1.42  tff('#skF_3', type, '#skF_3': $i).
% 2.88/1.42  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.88/1.42  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.88/1.42  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.88/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.88/1.42  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.88/1.42  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.88/1.42  tff('#skF_4', type, '#skF_4': $i).
% 2.88/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.88/1.42  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.88/1.42  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.88/1.42  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.88/1.42  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.88/1.42  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.88/1.42  
% 2.88/1.44  tff(f_111, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_2)).
% 2.88/1.44  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.88/1.44  tff(f_31, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.88/1.44  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.88/1.44  tff(f_29, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 2.88/1.44  tff(f_46, axiom, (![A, B]: ((k3_xboole_0(A, k1_tarski(B)) = k1_tarski(B)) => r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l29_zfmisc_1)).
% 2.88/1.44  tff(f_66, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.88/1.44  tff(f_78, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.88/1.44  tff(f_100, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 2.88/1.44  tff(f_82, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.88/1.44  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 2.88/1.44  tff(f_61, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, A), k2_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_funct_1)).
% 2.88/1.44  tff(f_53, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 2.88/1.44  tff(f_38, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 2.88/1.44  tff(c_52, plain, (k1_funct_1('#skF_6', '#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.88/1.44  tff(c_54, plain, (r2_hidden('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.88/1.44  tff(c_56, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.88/1.44  tff(c_187, plain, (![C_52, A_53, B_54]: (v1_relat_1(C_52) | ~m1_subset_1(C_52, k1_zfmisc_1(k2_zfmisc_1(A_53, B_54))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.88/1.44  tff(c_191, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_56, c_187])).
% 2.88/1.44  tff(c_60, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.88/1.44  tff(c_6, plain, (![A_4]: (r1_tarski(k1_xboole_0, A_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.88/1.44  tff(c_79, plain, (![B_42, A_43]: (k3_xboole_0(B_42, A_43)=k3_xboole_0(A_43, B_42))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.88/1.44  tff(c_4, plain, (![A_3]: (k3_xboole_0(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.88/1.44  tff(c_95, plain, (![A_43]: (k3_xboole_0(k1_xboole_0, A_43)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_79, c_4])).
% 2.88/1.44  tff(c_192, plain, (![B_55, A_56]: (r2_hidden(B_55, A_56) | k3_xboole_0(A_56, k1_tarski(B_55))!=k1_tarski(B_55))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.88/1.44  tff(c_205, plain, (![B_57]: (r2_hidden(B_57, k1_xboole_0) | k1_tarski(B_57)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_95, c_192])).
% 2.88/1.44  tff(c_30, plain, (![B_22, A_21]: (~r1_tarski(B_22, A_21) | ~r2_hidden(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.88/1.44  tff(c_208, plain, (![B_57]: (~r1_tarski(k1_xboole_0, B_57) | k1_tarski(B_57)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_205, c_30])).
% 2.88/1.44  tff(c_211, plain, (![B_57]: (k1_tarski(B_57)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_208])).
% 2.88/1.44  tff(c_58, plain, (v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.88/1.44  tff(c_260, plain, (![A_77, B_78, C_79]: (k1_relset_1(A_77, B_78, C_79)=k1_relat_1(C_79) | ~m1_subset_1(C_79, k1_zfmisc_1(k2_zfmisc_1(A_77, B_78))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.88/1.44  tff(c_264, plain, (k1_relset_1('#skF_3', k1_tarski('#skF_4'), '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_56, c_260])).
% 2.88/1.44  tff(c_504, plain, (![B_126, A_127, C_128]: (k1_xboole_0=B_126 | k1_relset_1(A_127, B_126, C_128)=A_127 | ~v1_funct_2(C_128, A_127, B_126) | ~m1_subset_1(C_128, k1_zfmisc_1(k2_zfmisc_1(A_127, B_126))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.88/1.44  tff(c_511, plain, (k1_tarski('#skF_4')=k1_xboole_0 | k1_relset_1('#skF_3', k1_tarski('#skF_4'), '#skF_6')='#skF_3' | ~v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_56, c_504])).
% 2.88/1.44  tff(c_515, plain, (k1_tarski('#skF_4')=k1_xboole_0 | k1_relat_1('#skF_6')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_264, c_511])).
% 2.88/1.44  tff(c_516, plain, (k1_relat_1('#skF_6')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_211, c_515])).
% 2.88/1.44  tff(c_251, plain, (![A_74, B_75, C_76]: (k2_relset_1(A_74, B_75, C_76)=k2_relat_1(C_76) | ~m1_subset_1(C_76, k1_zfmisc_1(k2_zfmisc_1(A_74, B_75))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.88/1.44  tff(c_255, plain, (k2_relset_1('#skF_3', k1_tarski('#skF_4'), '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_56, c_251])).
% 2.88/1.44  tff(c_290, plain, (![A_83, B_84, C_85]: (m1_subset_1(k2_relset_1(A_83, B_84, C_85), k1_zfmisc_1(B_84)) | ~m1_subset_1(C_85, k1_zfmisc_1(k2_zfmisc_1(A_83, B_84))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.88/1.44  tff(c_305, plain, (m1_subset_1(k2_relat_1('#skF_6'), k1_zfmisc_1(k1_tarski('#skF_4'))) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))))), inference(superposition, [status(thm), theory('equality')], [c_255, c_290])).
% 2.88/1.44  tff(c_310, plain, (m1_subset_1(k2_relat_1('#skF_6'), k1_zfmisc_1(k1_tarski('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_305])).
% 2.88/1.44  tff(c_368, plain, (![B_95, A_96]: (r2_hidden(k1_funct_1(B_95, A_96), k2_relat_1(B_95)) | ~r2_hidden(A_96, k1_relat_1(B_95)) | ~v1_funct_1(B_95) | ~v1_relat_1(B_95))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.88/1.44  tff(c_26, plain, (![C_18, A_15, B_16]: (r2_hidden(C_18, A_15) | ~r2_hidden(C_18, B_16) | ~m1_subset_1(B_16, k1_zfmisc_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.88/1.44  tff(c_530, plain, (![B_132, A_133, A_134]: (r2_hidden(k1_funct_1(B_132, A_133), A_134) | ~m1_subset_1(k2_relat_1(B_132), k1_zfmisc_1(A_134)) | ~r2_hidden(A_133, k1_relat_1(B_132)) | ~v1_funct_1(B_132) | ~v1_relat_1(B_132))), inference(resolution, [status(thm)], [c_368, c_26])).
% 2.88/1.44  tff(c_532, plain, (![A_133]: (r2_hidden(k1_funct_1('#skF_6', A_133), k1_tarski('#skF_4')) | ~r2_hidden(A_133, k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_310, c_530])).
% 2.88/1.44  tff(c_541, plain, (![A_139]: (r2_hidden(k1_funct_1('#skF_6', A_139), k1_tarski('#skF_4')) | ~r2_hidden(A_139, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_191, c_60, c_516, c_532])).
% 2.88/1.44  tff(c_8, plain, (![C_9, A_5]: (C_9=A_5 | ~r2_hidden(C_9, k1_tarski(A_5)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.88/1.44  tff(c_553, plain, (![A_140]: (k1_funct_1('#skF_6', A_140)='#skF_4' | ~r2_hidden(A_140, '#skF_3'))), inference(resolution, [status(thm)], [c_541, c_8])).
% 2.88/1.44  tff(c_568, plain, (k1_funct_1('#skF_6', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_54, c_553])).
% 2.88/1.44  tff(c_575, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_568])).
% 2.88/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.88/1.44  
% 2.88/1.44  Inference rules
% 2.88/1.44  ----------------------
% 2.88/1.44  #Ref     : 0
% 2.88/1.44  #Sup     : 112
% 2.88/1.44  #Fact    : 0
% 2.88/1.44  #Define  : 0
% 2.88/1.44  #Split   : 0
% 2.88/1.44  #Chain   : 0
% 2.88/1.44  #Close   : 0
% 2.88/1.44  
% 2.88/1.44  Ordering : KBO
% 2.88/1.44  
% 2.88/1.44  Simplification rules
% 2.88/1.44  ----------------------
% 2.88/1.44  #Subsume      : 12
% 2.88/1.44  #Demod        : 24
% 2.88/1.44  #Tautology    : 46
% 2.88/1.44  #SimpNegUnit  : 11
% 2.88/1.44  #BackRed      : 1
% 2.88/1.44  
% 2.88/1.44  #Partial instantiations: 0
% 2.88/1.44  #Strategies tried      : 1
% 2.88/1.44  
% 2.88/1.44  Timing (in seconds)
% 2.88/1.44  ----------------------
% 2.88/1.44  Preprocessing        : 0.33
% 2.88/1.44  Parsing              : 0.17
% 2.88/1.44  CNF conversion       : 0.02
% 2.88/1.44  Main loop            : 0.31
% 2.88/1.44  Inferencing          : 0.12
% 2.88/1.44  Reduction            : 0.09
% 2.88/1.44  Demodulation         : 0.06
% 2.88/1.44  BG Simplification    : 0.02
% 2.88/1.44  Subsumption          : 0.06
% 2.88/1.44  Abstraction          : 0.02
% 2.88/1.44  MUC search           : 0.00
% 2.88/1.44  Cooper               : 0.00
% 2.88/1.44  Total                : 0.67
% 2.88/1.44  Index Insertion      : 0.00
% 2.88/1.44  Index Deletion       : 0.00
% 2.88/1.44  Index Matching       : 0.00
% 2.88/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
