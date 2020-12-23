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
% DateTime   : Thu Dec  3 10:08:27 EST 2020

% Result     : Theorem 3.77s
% Output     : CNFRefutation 3.77s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 159 expanded)
%              Number of leaves         :   38 (  69 expanded)
%              Depth                    :   11
%              Number of atoms          :  113 ( 308 expanded)
%              Number of equality atoms :   31 (  74 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_112,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
               => ~ ( k2_relset_1(B,A,C) != k1_xboole_0
                    & ! [D] :
                        ( m1_subset_1(D,B)
                       => ~ r2_hidden(D,k1_relset_1(B,A,C)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_relset_1)).

tff(f_66,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_58,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_72,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_34,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

tff(f_77,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_91,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(c_52,plain,(
    k2_relset_1('#skF_6','#skF_5','#skF_7') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_34,plain,(
    ! [A_20,B_21] : v1_relat_1(k2_zfmisc_1(A_20,B_21)) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_54,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_85,plain,(
    ! [B_63,A_64] :
      ( v1_relat_1(B_63)
      | ~ m1_subset_1(B_63,k1_zfmisc_1(A_64))
      | ~ v1_relat_1(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_91,plain,
    ( v1_relat_1('#skF_7')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_6','#skF_5')) ),
    inference(resolution,[status(thm)],[c_54,c_85])).

tff(c_95,plain,(
    v1_relat_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_91])).

tff(c_165,plain,(
    ! [C_79,A_80,B_81] :
      ( v4_relat_1(C_79,A_80)
      | ~ m1_subset_1(C_79,k1_zfmisc_1(k2_zfmisc_1(A_80,B_81))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_174,plain,(
    v4_relat_1('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_54,c_165])).

tff(c_32,plain,(
    ! [B_19,A_18] :
      ( r1_tarski(k1_relat_1(B_19),A_18)
      | ~ v4_relat_1(B_19,A_18)
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_36,plain,(
    ! [A_22] :
      ( k1_relat_1(A_22) = k1_xboole_0
      | k2_relat_1(A_22) != k1_xboole_0
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_107,plain,
    ( k1_relat_1('#skF_7') = k1_xboole_0
    | k2_relat_1('#skF_7') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_95,c_36])).

tff(c_109,plain,(
    k2_relat_1('#skF_7') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_107])).

tff(c_38,plain,(
    ! [A_22] :
      ( k2_relat_1(A_22) = k1_xboole_0
      | k1_relat_1(A_22) != k1_xboole_0
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_108,plain,
    ( k2_relat_1('#skF_7') = k1_xboole_0
    | k1_relat_1('#skF_7') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_95,c_38])).

tff(c_110,plain,(
    k1_relat_1('#skF_7') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_109,c_108])).

tff(c_10,plain,(
    ! [A_4] : r1_tarski(k1_xboole_0,A_4) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_344,plain,(
    ! [A_121,B_122] :
      ( r2_hidden('#skF_1'(A_121,B_122),B_122)
      | r2_hidden('#skF_2'(A_121,B_122),A_121)
      | B_122 = A_121 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_40,plain,(
    ! [B_24,A_23] :
      ( ~ r1_tarski(B_24,A_23)
      | ~ r2_hidden(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_657,plain,(
    ! [A_148,B_149] :
      ( ~ r1_tarski(A_148,'#skF_2'(A_148,B_149))
      | r2_hidden('#skF_1'(A_148,B_149),B_149)
      | B_149 = A_148 ) ),
    inference(resolution,[status(thm)],[c_344,c_40])).

tff(c_696,plain,(
    ! [B_151] :
      ( r2_hidden('#skF_1'(k1_xboole_0,B_151),B_151)
      | k1_xboole_0 = B_151 ) ),
    inference(resolution,[status(thm)],[c_10,c_657])).

tff(c_65,plain,(
    ! [C_56,A_57] :
      ( r2_hidden(C_56,k1_zfmisc_1(A_57))
      | ~ r1_tarski(C_56,A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_24,plain,(
    ! [A_10,B_11] :
      ( m1_subset_1(A_10,B_11)
      | ~ r2_hidden(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_77,plain,(
    ! [C_56,A_57] :
      ( m1_subset_1(C_56,k1_zfmisc_1(A_57))
      | ~ r1_tarski(C_56,A_57) ) ),
    inference(resolution,[status(thm)],[c_65,c_24])).

tff(c_175,plain,(
    ! [A_82,C_83,B_84] :
      ( m1_subset_1(A_82,C_83)
      | ~ m1_subset_1(B_84,k1_zfmisc_1(C_83))
      | ~ r2_hidden(A_82,B_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_180,plain,(
    ! [A_82,A_57,C_56] :
      ( m1_subset_1(A_82,A_57)
      | ~ r2_hidden(A_82,C_56)
      | ~ r1_tarski(C_56,A_57) ) ),
    inference(resolution,[status(thm)],[c_77,c_175])).

tff(c_825,plain,(
    ! [B_157,A_158] :
      ( m1_subset_1('#skF_1'(k1_xboole_0,B_157),A_158)
      | ~ r1_tarski(B_157,A_158)
      | k1_xboole_0 = B_157 ) ),
    inference(resolution,[status(thm)],[c_696,c_180])).

tff(c_230,plain,(
    ! [A_104,B_105,C_106] :
      ( k1_relset_1(A_104,B_105,C_106) = k1_relat_1(C_106)
      | ~ m1_subset_1(C_106,k1_zfmisc_1(k2_zfmisc_1(A_104,B_105))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_239,plain,(
    k1_relset_1('#skF_6','#skF_5','#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_54,c_230])).

tff(c_50,plain,(
    ! [D_45] :
      ( ~ r2_hidden(D_45,k1_relset_1('#skF_6','#skF_5','#skF_7'))
      | ~ m1_subset_1(D_45,'#skF_6') ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_257,plain,(
    ! [D_45] :
      ( ~ r2_hidden(D_45,k1_relat_1('#skF_7'))
      | ~ m1_subset_1(D_45,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_239,c_50])).

tff(c_704,plain,
    ( ~ m1_subset_1('#skF_1'(k1_xboole_0,k1_relat_1('#skF_7')),'#skF_6')
    | k1_relat_1('#skF_7') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_696,c_257])).

tff(c_726,plain,(
    ~ m1_subset_1('#skF_1'(k1_xboole_0,k1_relat_1('#skF_7')),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_110,c_704])).

tff(c_828,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_7'),'#skF_6')
    | k1_relat_1('#skF_7') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_825,c_726])).

tff(c_854,plain,(
    ~ r1_tarski(k1_relat_1('#skF_7'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_110,c_828])).

tff(c_863,plain,
    ( ~ v4_relat_1('#skF_7','#skF_6')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_32,c_854])).

tff(c_867,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_174,c_863])).

tff(c_868,plain,(
    k1_relat_1('#skF_7') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_107])).

tff(c_875,plain,(
    k2_relat_1('#skF_7') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_868,c_108])).

tff(c_1027,plain,(
    ! [A_200,B_201,C_202] :
      ( k2_relset_1(A_200,B_201,C_202) = k2_relat_1(C_202)
      | ~ m1_subset_1(C_202,k1_zfmisc_1(k2_zfmisc_1(A_200,B_201))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1034,plain,(
    k2_relset_1('#skF_6','#skF_5','#skF_7') = k2_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_54,c_1027])).

tff(c_1037,plain,(
    k2_relset_1('#skF_6','#skF_5','#skF_7') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_875,c_1034])).

tff(c_1039,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_1037])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:52:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.77/1.98  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.77/1.98  
% 3.77/1.98  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.77/1.99  %$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1 > #skF_4
% 3.77/1.99  
% 3.77/1.99  %Foreground sorts:
% 3.77/1.99  
% 3.77/1.99  
% 3.77/1.99  %Background operators:
% 3.77/1.99  
% 3.77/1.99  
% 3.77/1.99  %Foreground operators:
% 3.77/1.99  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.77/1.99  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.77/1.99  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.77/1.99  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.77/1.99  tff('#skF_7', type, '#skF_7': $i).
% 3.77/1.99  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.77/1.99  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.77/1.99  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.77/1.99  tff('#skF_5', type, '#skF_5': $i).
% 3.77/1.99  tff('#skF_6', type, '#skF_6': $i).
% 3.77/1.99  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.77/1.99  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.77/1.99  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.77/1.99  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.77/1.99  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.77/1.99  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.77/1.99  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.77/1.99  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.77/1.99  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.77/1.99  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.77/1.99  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.77/1.99  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.77/1.99  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.77/1.99  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.77/1.99  
% 3.77/2.00  tff(f_112, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ~(~(k2_relset_1(B, A, C) = k1_xboole_0) & (![D]: (m1_subset_1(D, B) => ~r2_hidden(D, k1_relset_1(B, A, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_relset_1)).
% 3.77/2.00  tff(f_66, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.77/2.00  tff(f_58, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.77/2.00  tff(f_83, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.77/2.00  tff(f_64, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 3.77/2.00  tff(f_72, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_relat_1)).
% 3.77/2.00  tff(f_34, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.77/2.00  tff(f_32, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tarski)).
% 3.77/2.00  tff(f_77, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.77/2.00  tff(f_41, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 3.77/2.00  tff(f_45, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 3.77/2.00  tff(f_51, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 3.77/2.00  tff(f_87, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.77/2.00  tff(f_91, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.77/2.00  tff(c_52, plain, (k2_relset_1('#skF_6', '#skF_5', '#skF_7')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.77/2.00  tff(c_34, plain, (![A_20, B_21]: (v1_relat_1(k2_zfmisc_1(A_20, B_21)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.77/2.00  tff(c_54, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.77/2.00  tff(c_85, plain, (![B_63, A_64]: (v1_relat_1(B_63) | ~m1_subset_1(B_63, k1_zfmisc_1(A_64)) | ~v1_relat_1(A_64))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.77/2.00  tff(c_91, plain, (v1_relat_1('#skF_7') | ~v1_relat_1(k2_zfmisc_1('#skF_6', '#skF_5'))), inference(resolution, [status(thm)], [c_54, c_85])).
% 3.77/2.00  tff(c_95, plain, (v1_relat_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_91])).
% 3.77/2.00  tff(c_165, plain, (![C_79, A_80, B_81]: (v4_relat_1(C_79, A_80) | ~m1_subset_1(C_79, k1_zfmisc_1(k2_zfmisc_1(A_80, B_81))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.77/2.00  tff(c_174, plain, (v4_relat_1('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_54, c_165])).
% 3.77/2.00  tff(c_32, plain, (![B_19, A_18]: (r1_tarski(k1_relat_1(B_19), A_18) | ~v4_relat_1(B_19, A_18) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.77/2.00  tff(c_36, plain, (![A_22]: (k1_relat_1(A_22)=k1_xboole_0 | k2_relat_1(A_22)!=k1_xboole_0 | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.77/2.00  tff(c_107, plain, (k1_relat_1('#skF_7')=k1_xboole_0 | k2_relat_1('#skF_7')!=k1_xboole_0), inference(resolution, [status(thm)], [c_95, c_36])).
% 3.77/2.00  tff(c_109, plain, (k2_relat_1('#skF_7')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_107])).
% 3.77/2.00  tff(c_38, plain, (![A_22]: (k2_relat_1(A_22)=k1_xboole_0 | k1_relat_1(A_22)!=k1_xboole_0 | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.77/2.00  tff(c_108, plain, (k2_relat_1('#skF_7')=k1_xboole_0 | k1_relat_1('#skF_7')!=k1_xboole_0), inference(resolution, [status(thm)], [c_95, c_38])).
% 3.77/2.00  tff(c_110, plain, (k1_relat_1('#skF_7')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_109, c_108])).
% 3.77/2.00  tff(c_10, plain, (![A_4]: (r1_tarski(k1_xboole_0, A_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.77/2.00  tff(c_344, plain, (![A_121, B_122]: (r2_hidden('#skF_1'(A_121, B_122), B_122) | r2_hidden('#skF_2'(A_121, B_122), A_121) | B_122=A_121)), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.77/2.00  tff(c_40, plain, (![B_24, A_23]: (~r1_tarski(B_24, A_23) | ~r2_hidden(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.77/2.00  tff(c_657, plain, (![A_148, B_149]: (~r1_tarski(A_148, '#skF_2'(A_148, B_149)) | r2_hidden('#skF_1'(A_148, B_149), B_149) | B_149=A_148)), inference(resolution, [status(thm)], [c_344, c_40])).
% 3.77/2.00  tff(c_696, plain, (![B_151]: (r2_hidden('#skF_1'(k1_xboole_0, B_151), B_151) | k1_xboole_0=B_151)), inference(resolution, [status(thm)], [c_10, c_657])).
% 3.77/2.00  tff(c_65, plain, (![C_56, A_57]: (r2_hidden(C_56, k1_zfmisc_1(A_57)) | ~r1_tarski(C_56, A_57))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.77/2.00  tff(c_24, plain, (![A_10, B_11]: (m1_subset_1(A_10, B_11) | ~r2_hidden(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.77/2.00  tff(c_77, plain, (![C_56, A_57]: (m1_subset_1(C_56, k1_zfmisc_1(A_57)) | ~r1_tarski(C_56, A_57))), inference(resolution, [status(thm)], [c_65, c_24])).
% 3.77/2.00  tff(c_175, plain, (![A_82, C_83, B_84]: (m1_subset_1(A_82, C_83) | ~m1_subset_1(B_84, k1_zfmisc_1(C_83)) | ~r2_hidden(A_82, B_84))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.77/2.00  tff(c_180, plain, (![A_82, A_57, C_56]: (m1_subset_1(A_82, A_57) | ~r2_hidden(A_82, C_56) | ~r1_tarski(C_56, A_57))), inference(resolution, [status(thm)], [c_77, c_175])).
% 3.77/2.00  tff(c_825, plain, (![B_157, A_158]: (m1_subset_1('#skF_1'(k1_xboole_0, B_157), A_158) | ~r1_tarski(B_157, A_158) | k1_xboole_0=B_157)), inference(resolution, [status(thm)], [c_696, c_180])).
% 3.77/2.00  tff(c_230, plain, (![A_104, B_105, C_106]: (k1_relset_1(A_104, B_105, C_106)=k1_relat_1(C_106) | ~m1_subset_1(C_106, k1_zfmisc_1(k2_zfmisc_1(A_104, B_105))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.77/2.00  tff(c_239, plain, (k1_relset_1('#skF_6', '#skF_5', '#skF_7')=k1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_54, c_230])).
% 3.77/2.00  tff(c_50, plain, (![D_45]: (~r2_hidden(D_45, k1_relset_1('#skF_6', '#skF_5', '#skF_7')) | ~m1_subset_1(D_45, '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.77/2.00  tff(c_257, plain, (![D_45]: (~r2_hidden(D_45, k1_relat_1('#skF_7')) | ~m1_subset_1(D_45, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_239, c_50])).
% 3.77/2.00  tff(c_704, plain, (~m1_subset_1('#skF_1'(k1_xboole_0, k1_relat_1('#skF_7')), '#skF_6') | k1_relat_1('#skF_7')=k1_xboole_0), inference(resolution, [status(thm)], [c_696, c_257])).
% 3.77/2.00  tff(c_726, plain, (~m1_subset_1('#skF_1'(k1_xboole_0, k1_relat_1('#skF_7')), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_110, c_704])).
% 3.77/2.00  tff(c_828, plain, (~r1_tarski(k1_relat_1('#skF_7'), '#skF_6') | k1_relat_1('#skF_7')=k1_xboole_0), inference(resolution, [status(thm)], [c_825, c_726])).
% 3.77/2.00  tff(c_854, plain, (~r1_tarski(k1_relat_1('#skF_7'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_110, c_828])).
% 3.77/2.00  tff(c_863, plain, (~v4_relat_1('#skF_7', '#skF_6') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_32, c_854])).
% 3.77/2.00  tff(c_867, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_95, c_174, c_863])).
% 3.77/2.00  tff(c_868, plain, (k1_relat_1('#skF_7')=k1_xboole_0), inference(splitRight, [status(thm)], [c_107])).
% 3.77/2.00  tff(c_875, plain, (k2_relat_1('#skF_7')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_868, c_108])).
% 3.77/2.00  tff(c_1027, plain, (![A_200, B_201, C_202]: (k2_relset_1(A_200, B_201, C_202)=k2_relat_1(C_202) | ~m1_subset_1(C_202, k1_zfmisc_1(k2_zfmisc_1(A_200, B_201))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.77/2.00  tff(c_1034, plain, (k2_relset_1('#skF_6', '#skF_5', '#skF_7')=k2_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_54, c_1027])).
% 3.77/2.00  tff(c_1037, plain, (k2_relset_1('#skF_6', '#skF_5', '#skF_7')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_875, c_1034])).
% 3.77/2.00  tff(c_1039, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_1037])).
% 3.77/2.00  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.77/2.00  
% 3.77/2.00  Inference rules
% 3.77/2.00  ----------------------
% 3.77/2.00  #Ref     : 0
% 3.77/2.00  #Sup     : 184
% 3.77/2.00  #Fact    : 0
% 3.77/2.00  #Define  : 0
% 3.77/2.00  #Split   : 12
% 3.77/2.00  #Chain   : 0
% 3.77/2.00  #Close   : 0
% 3.77/2.00  
% 3.77/2.00  Ordering : KBO
% 3.77/2.00  
% 3.77/2.00  Simplification rules
% 3.77/2.00  ----------------------
% 3.77/2.00  #Subsume      : 44
% 3.77/2.00  #Demod        : 29
% 3.77/2.00  #Tautology    : 37
% 3.77/2.00  #SimpNegUnit  : 43
% 3.77/2.00  #BackRed      : 21
% 3.77/2.00  
% 3.77/2.00  #Partial instantiations: 0
% 3.77/2.00  #Strategies tried      : 1
% 3.77/2.00  
% 3.77/2.00  Timing (in seconds)
% 3.77/2.00  ----------------------
% 3.77/2.00  Preprocessing        : 0.51
% 3.77/2.00  Parsing              : 0.26
% 3.77/2.00  CNF conversion       : 0.04
% 3.77/2.00  Main loop            : 0.60
% 3.77/2.01  Inferencing          : 0.21
% 3.77/2.01  Reduction            : 0.18
% 3.77/2.01  Demodulation         : 0.12
% 3.77/2.01  BG Simplification    : 0.03
% 3.77/2.01  Subsumption          : 0.11
% 3.77/2.01  Abstraction          : 0.03
% 3.77/2.01  MUC search           : 0.00
% 3.77/2.01  Cooper               : 0.00
% 3.77/2.01  Total                : 1.16
% 3.77/2.01  Index Insertion      : 0.00
% 3.77/2.01  Index Deletion       : 0.00
% 3.77/2.01  Index Matching       : 0.00
% 3.77/2.01  BG Taut test         : 0.00
%------------------------------------------------------------------------------
