%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:28 EST 2020

% Result     : Theorem 3.84s
% Output     : CNFRefutation 3.84s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 159 expanded)
%              Number of leaves         :   41 (  70 expanded)
%              Depth                    :   11
%              Number of atoms          :  131 ( 304 expanded)
%              Number of equality atoms :   42 (  77 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k3_tarski > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_8 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_118,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_relset_1)).

tff(f_77,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_69,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_83,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_89,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_48,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_45,axiom,(
    ! [A] : k3_tarski(k1_zfmisc_1(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).

tff(f_33,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_58,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_43,axiom,(
    ! [A,B] :
      ( B = k3_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] :
              ( r2_hidden(C,D)
              & r2_hidden(D,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tarski)).

tff(f_52,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_93,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_97,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(c_56,plain,(
    k2_relset_1('#skF_7','#skF_6','#skF_8') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_40,plain,(
    ! [A_35,B_36] : v1_relat_1(k2_zfmisc_1(A_35,B_36)) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_58,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_107,plain,(
    ! [B_73,A_74] :
      ( v1_relat_1(B_73)
      | ~ m1_subset_1(B_73,k1_zfmisc_1(A_74))
      | ~ v1_relat_1(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_117,plain,
    ( v1_relat_1('#skF_8')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_7','#skF_6')) ),
    inference(resolution,[status(thm)],[c_58,c_107])).

tff(c_122,plain,(
    v1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_117])).

tff(c_42,plain,(
    ! [A_37] :
      ( k1_relat_1(A_37) = k1_xboole_0
      | k2_relat_1(A_37) != k1_xboole_0
      | ~ v1_relat_1(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_126,plain,
    ( k1_relat_1('#skF_8') = k1_xboole_0
    | k2_relat_1('#skF_8') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_122,c_42])).

tff(c_127,plain,(
    k2_relat_1('#skF_8') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_126])).

tff(c_818,plain,(
    ! [A_179] :
      ( k2_relat_1(A_179) = k1_xboole_0
      | k1_relat_1(A_179) != k1_xboole_0
      | ~ v1_relat_1(A_179) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_821,plain,
    ( k2_relat_1('#skF_8') = k1_xboole_0
    | k1_relat_1('#skF_8') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_122,c_818])).

tff(c_827,plain,(
    k1_relat_1('#skF_8') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_127,c_821])).

tff(c_199,plain,(
    ! [C_89,A_90,B_91] :
      ( v4_relat_1(C_89,A_90)
      | ~ m1_subset_1(C_89,k1_zfmisc_1(k2_zfmisc_1(A_90,B_91))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_213,plain,(
    v4_relat_1('#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_58,c_199])).

tff(c_38,plain,(
    ! [B_34,A_33] :
      ( r1_tarski(k1_relat_1(B_34),A_33)
      | ~ v4_relat_1(B_34,A_33)
      | ~ v1_relat_1(B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_32,plain,(
    ! [A_28,B_29] :
      ( m1_subset_1(A_28,k1_zfmisc_1(B_29))
      | ~ r1_tarski(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_136,plain,(
    ! [A_77] :
      ( k2_relat_1(A_77) = k1_xboole_0
      | k1_relat_1(A_77) != k1_xboole_0
      | ~ v1_relat_1(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_139,plain,
    ( k2_relat_1('#skF_8') = k1_xboole_0
    | k1_relat_1('#skF_8') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_122,c_136])).

tff(c_145,plain,(
    k1_relat_1('#skF_8') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_127,c_139])).

tff(c_24,plain,(
    ! [A_23] : ~ v1_xboole_0(k1_zfmisc_1(A_23)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_22,plain,(
    ! [A_22] : k3_tarski(k1_zfmisc_1(A_22)) = A_22 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_28,plain,(
    ! [A_26,B_27] :
      ( r2_hidden(A_26,B_27)
      | v1_xboole_0(B_27)
      | ~ m1_subset_1(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_235,plain,(
    ! [C_97,A_98,D_99] :
      ( r2_hidden(C_97,k3_tarski(A_98))
      | ~ r2_hidden(D_99,A_98)
      | ~ r2_hidden(C_97,D_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_640,plain,(
    ! [C_159,B_160,A_161] :
      ( r2_hidden(C_159,k3_tarski(B_160))
      | ~ r2_hidden(C_159,A_161)
      | v1_xboole_0(B_160)
      | ~ m1_subset_1(A_161,B_160) ) ),
    inference(resolution,[status(thm)],[c_28,c_235])).

tff(c_681,plain,(
    ! [A_166,B_167] :
      ( r2_hidden('#skF_1'(A_166),k3_tarski(B_167))
      | v1_xboole_0(B_167)
      | ~ m1_subset_1(A_166,B_167)
      | k1_xboole_0 = A_166 ) ),
    inference(resolution,[status(thm)],[c_2,c_640])).

tff(c_691,plain,(
    ! [A_166,A_22] :
      ( r2_hidden('#skF_1'(A_166),A_22)
      | v1_xboole_0(k1_zfmisc_1(A_22))
      | ~ m1_subset_1(A_166,k1_zfmisc_1(A_22))
      | k1_xboole_0 = A_166 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_681])).

tff(c_696,plain,(
    ! [A_168,A_169] :
      ( r2_hidden('#skF_1'(A_168),A_169)
      | ~ m1_subset_1(A_168,k1_zfmisc_1(A_169))
      | k1_xboole_0 = A_168 ) ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_691])).

tff(c_26,plain,(
    ! [A_24,B_25] :
      ( m1_subset_1(A_24,B_25)
      | ~ r2_hidden(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_722,plain,(
    ! [A_170,A_171] :
      ( m1_subset_1('#skF_1'(A_170),A_171)
      | ~ m1_subset_1(A_170,k1_zfmisc_1(A_171))
      | k1_xboole_0 = A_170 ) ),
    inference(resolution,[status(thm)],[c_696,c_26])).

tff(c_407,plain,(
    ! [A_129,B_130,C_131] :
      ( k1_relset_1(A_129,B_130,C_131) = k1_relat_1(C_131)
      | ~ m1_subset_1(C_131,k1_zfmisc_1(k2_zfmisc_1(A_129,B_130))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_427,plain,(
    k1_relset_1('#skF_7','#skF_6','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_58,c_407])).

tff(c_80,plain,(
    ! [D_66] :
      ( ~ r2_hidden(D_66,k1_relset_1('#skF_7','#skF_6','#skF_8'))
      | ~ m1_subset_1(D_66,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_85,plain,
    ( ~ m1_subset_1('#skF_1'(k1_relset_1('#skF_7','#skF_6','#skF_8')),'#skF_7')
    | k1_relset_1('#skF_7','#skF_6','#skF_8') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_80])).

tff(c_128,plain,(
    ~ m1_subset_1('#skF_1'(k1_relset_1('#skF_7','#skF_6','#skF_8')),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_85])).

tff(c_430,plain,(
    ~ m1_subset_1('#skF_1'(k1_relat_1('#skF_8')),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_427,c_128])).

tff(c_733,plain,
    ( ~ m1_subset_1(k1_relat_1('#skF_8'),k1_zfmisc_1('#skF_7'))
    | k1_relat_1('#skF_8') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_722,c_430])).

tff(c_758,plain,(
    ~ m1_subset_1(k1_relat_1('#skF_8'),k1_zfmisc_1('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_145,c_733])).

tff(c_767,plain,(
    ~ r1_tarski(k1_relat_1('#skF_8'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_32,c_758])).

tff(c_781,plain,
    ( ~ v4_relat_1('#skF_8','#skF_7')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_38,c_767])).

tff(c_785,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_213,c_781])).

tff(c_786,plain,(
    k1_relset_1('#skF_7','#skF_6','#skF_8') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_85])).

tff(c_1162,plain,(
    ! [A_239,B_240,C_241] :
      ( k1_relset_1(A_239,B_240,C_241) = k1_relat_1(C_241)
      | ~ m1_subset_1(C_241,k1_zfmisc_1(k2_zfmisc_1(A_239,B_240))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_1181,plain,(
    k1_relset_1('#skF_7','#skF_6','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_58,c_1162])).

tff(c_1188,plain,(
    k1_relat_1('#skF_8') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_786,c_1181])).

tff(c_1190,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_827,c_1188])).

tff(c_1192,plain,(
    k2_relat_1('#skF_8') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_126])).

tff(c_1552,plain,(
    ! [A_301,B_302,C_303] :
      ( k2_relset_1(A_301,B_302,C_303) = k2_relat_1(C_303)
      | ~ m1_subset_1(C_303,k1_zfmisc_1(k2_zfmisc_1(A_301,B_302))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_1567,plain,(
    k2_relset_1('#skF_7','#skF_6','#skF_8') = k2_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_58,c_1552])).

tff(c_1573,plain,(
    k2_relset_1('#skF_7','#skF_6','#skF_8') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1192,c_1567])).

tff(c_1575,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_1573])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n015.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 19:30:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.84/1.74  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.84/1.75  
% 3.84/1.75  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.84/1.75  %$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k3_tarski > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_8 > #skF_2 > #skF_4
% 3.84/1.75  
% 3.84/1.75  %Foreground sorts:
% 3.84/1.75  
% 3.84/1.75  
% 3.84/1.75  %Background operators:
% 3.84/1.75  
% 3.84/1.75  
% 3.84/1.75  %Foreground operators:
% 3.84/1.75  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.84/1.75  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.84/1.75  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.84/1.75  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.84/1.75  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.84/1.75  tff('#skF_7', type, '#skF_7': $i).
% 3.84/1.75  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.84/1.75  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.84/1.75  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.84/1.75  tff('#skF_6', type, '#skF_6': $i).
% 3.84/1.75  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 3.84/1.75  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.84/1.75  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.84/1.75  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.84/1.75  tff('#skF_8', type, '#skF_8': $i).
% 3.84/1.75  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.84/1.75  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.84/1.75  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.84/1.75  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.84/1.75  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.84/1.75  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.84/1.75  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.84/1.75  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.84/1.75  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.84/1.75  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.84/1.75  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.84/1.75  
% 3.84/1.77  tff(f_118, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ~(~(k2_relset_1(B, A, C) = k1_xboole_0) & (![D]: (m1_subset_1(D, B) => ~r2_hidden(D, k1_relset_1(B, A, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_relset_1)).
% 3.84/1.77  tff(f_77, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.84/1.77  tff(f_69, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.84/1.77  tff(f_83, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_relat_1)).
% 3.84/1.77  tff(f_89, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.84/1.77  tff(f_75, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 3.84/1.77  tff(f_62, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.84/1.77  tff(f_48, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 3.84/1.77  tff(f_45, axiom, (![A]: (k3_tarski(k1_zfmisc_1(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 3.84/1.77  tff(f_33, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.84/1.77  tff(f_58, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 3.84/1.77  tff(f_43, axiom, (![A, B]: ((B = k3_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(C, D) & r2_hidden(D, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tarski)).
% 3.84/1.77  tff(f_52, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 3.84/1.77  tff(f_93, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.84/1.77  tff(f_97, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.84/1.77  tff(c_56, plain, (k2_relset_1('#skF_7', '#skF_6', '#skF_8')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.84/1.77  tff(c_40, plain, (![A_35, B_36]: (v1_relat_1(k2_zfmisc_1(A_35, B_36)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.84/1.77  tff(c_58, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_7', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.84/1.77  tff(c_107, plain, (![B_73, A_74]: (v1_relat_1(B_73) | ~m1_subset_1(B_73, k1_zfmisc_1(A_74)) | ~v1_relat_1(A_74))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.84/1.77  tff(c_117, plain, (v1_relat_1('#skF_8') | ~v1_relat_1(k2_zfmisc_1('#skF_7', '#skF_6'))), inference(resolution, [status(thm)], [c_58, c_107])).
% 3.84/1.77  tff(c_122, plain, (v1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_117])).
% 3.84/1.77  tff(c_42, plain, (![A_37]: (k1_relat_1(A_37)=k1_xboole_0 | k2_relat_1(A_37)!=k1_xboole_0 | ~v1_relat_1(A_37))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.84/1.77  tff(c_126, plain, (k1_relat_1('#skF_8')=k1_xboole_0 | k2_relat_1('#skF_8')!=k1_xboole_0), inference(resolution, [status(thm)], [c_122, c_42])).
% 3.84/1.77  tff(c_127, plain, (k2_relat_1('#skF_8')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_126])).
% 3.84/1.77  tff(c_818, plain, (![A_179]: (k2_relat_1(A_179)=k1_xboole_0 | k1_relat_1(A_179)!=k1_xboole_0 | ~v1_relat_1(A_179))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.84/1.77  tff(c_821, plain, (k2_relat_1('#skF_8')=k1_xboole_0 | k1_relat_1('#skF_8')!=k1_xboole_0), inference(resolution, [status(thm)], [c_122, c_818])).
% 3.84/1.77  tff(c_827, plain, (k1_relat_1('#skF_8')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_127, c_821])).
% 3.84/1.77  tff(c_199, plain, (![C_89, A_90, B_91]: (v4_relat_1(C_89, A_90) | ~m1_subset_1(C_89, k1_zfmisc_1(k2_zfmisc_1(A_90, B_91))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.84/1.77  tff(c_213, plain, (v4_relat_1('#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_58, c_199])).
% 3.84/1.77  tff(c_38, plain, (![B_34, A_33]: (r1_tarski(k1_relat_1(B_34), A_33) | ~v4_relat_1(B_34, A_33) | ~v1_relat_1(B_34))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.84/1.77  tff(c_32, plain, (![A_28, B_29]: (m1_subset_1(A_28, k1_zfmisc_1(B_29)) | ~r1_tarski(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.84/1.77  tff(c_136, plain, (![A_77]: (k2_relat_1(A_77)=k1_xboole_0 | k1_relat_1(A_77)!=k1_xboole_0 | ~v1_relat_1(A_77))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.84/1.77  tff(c_139, plain, (k2_relat_1('#skF_8')=k1_xboole_0 | k1_relat_1('#skF_8')!=k1_xboole_0), inference(resolution, [status(thm)], [c_122, c_136])).
% 3.84/1.77  tff(c_145, plain, (k1_relat_1('#skF_8')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_127, c_139])).
% 3.84/1.77  tff(c_24, plain, (![A_23]: (~v1_xboole_0(k1_zfmisc_1(A_23)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.84/1.77  tff(c_22, plain, (![A_22]: (k3_tarski(k1_zfmisc_1(A_22))=A_22)), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.84/1.77  tff(c_2, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.84/1.77  tff(c_28, plain, (![A_26, B_27]: (r2_hidden(A_26, B_27) | v1_xboole_0(B_27) | ~m1_subset_1(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.84/1.77  tff(c_235, plain, (![C_97, A_98, D_99]: (r2_hidden(C_97, k3_tarski(A_98)) | ~r2_hidden(D_99, A_98) | ~r2_hidden(C_97, D_99))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.84/1.77  tff(c_640, plain, (![C_159, B_160, A_161]: (r2_hidden(C_159, k3_tarski(B_160)) | ~r2_hidden(C_159, A_161) | v1_xboole_0(B_160) | ~m1_subset_1(A_161, B_160))), inference(resolution, [status(thm)], [c_28, c_235])).
% 3.84/1.77  tff(c_681, plain, (![A_166, B_167]: (r2_hidden('#skF_1'(A_166), k3_tarski(B_167)) | v1_xboole_0(B_167) | ~m1_subset_1(A_166, B_167) | k1_xboole_0=A_166)), inference(resolution, [status(thm)], [c_2, c_640])).
% 3.84/1.77  tff(c_691, plain, (![A_166, A_22]: (r2_hidden('#skF_1'(A_166), A_22) | v1_xboole_0(k1_zfmisc_1(A_22)) | ~m1_subset_1(A_166, k1_zfmisc_1(A_22)) | k1_xboole_0=A_166)), inference(superposition, [status(thm), theory('equality')], [c_22, c_681])).
% 3.84/1.77  tff(c_696, plain, (![A_168, A_169]: (r2_hidden('#skF_1'(A_168), A_169) | ~m1_subset_1(A_168, k1_zfmisc_1(A_169)) | k1_xboole_0=A_168)), inference(negUnitSimplification, [status(thm)], [c_24, c_691])).
% 3.84/1.77  tff(c_26, plain, (![A_24, B_25]: (m1_subset_1(A_24, B_25) | ~r2_hidden(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.84/1.77  tff(c_722, plain, (![A_170, A_171]: (m1_subset_1('#skF_1'(A_170), A_171) | ~m1_subset_1(A_170, k1_zfmisc_1(A_171)) | k1_xboole_0=A_170)), inference(resolution, [status(thm)], [c_696, c_26])).
% 3.84/1.77  tff(c_407, plain, (![A_129, B_130, C_131]: (k1_relset_1(A_129, B_130, C_131)=k1_relat_1(C_131) | ~m1_subset_1(C_131, k1_zfmisc_1(k2_zfmisc_1(A_129, B_130))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.84/1.77  tff(c_427, plain, (k1_relset_1('#skF_7', '#skF_6', '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_58, c_407])).
% 3.84/1.77  tff(c_80, plain, (![D_66]: (~r2_hidden(D_66, k1_relset_1('#skF_7', '#skF_6', '#skF_8')) | ~m1_subset_1(D_66, '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.84/1.77  tff(c_85, plain, (~m1_subset_1('#skF_1'(k1_relset_1('#skF_7', '#skF_6', '#skF_8')), '#skF_7') | k1_relset_1('#skF_7', '#skF_6', '#skF_8')=k1_xboole_0), inference(resolution, [status(thm)], [c_2, c_80])).
% 3.84/1.77  tff(c_128, plain, (~m1_subset_1('#skF_1'(k1_relset_1('#skF_7', '#skF_6', '#skF_8')), '#skF_7')), inference(splitLeft, [status(thm)], [c_85])).
% 3.84/1.77  tff(c_430, plain, (~m1_subset_1('#skF_1'(k1_relat_1('#skF_8')), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_427, c_128])).
% 3.84/1.77  tff(c_733, plain, (~m1_subset_1(k1_relat_1('#skF_8'), k1_zfmisc_1('#skF_7')) | k1_relat_1('#skF_8')=k1_xboole_0), inference(resolution, [status(thm)], [c_722, c_430])).
% 3.84/1.77  tff(c_758, plain, (~m1_subset_1(k1_relat_1('#skF_8'), k1_zfmisc_1('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_145, c_733])).
% 3.84/1.77  tff(c_767, plain, (~r1_tarski(k1_relat_1('#skF_8'), '#skF_7')), inference(resolution, [status(thm)], [c_32, c_758])).
% 3.84/1.77  tff(c_781, plain, (~v4_relat_1('#skF_8', '#skF_7') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_38, c_767])).
% 3.84/1.77  tff(c_785, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_122, c_213, c_781])).
% 3.84/1.77  tff(c_786, plain, (k1_relset_1('#skF_7', '#skF_6', '#skF_8')=k1_xboole_0), inference(splitRight, [status(thm)], [c_85])).
% 3.84/1.77  tff(c_1162, plain, (![A_239, B_240, C_241]: (k1_relset_1(A_239, B_240, C_241)=k1_relat_1(C_241) | ~m1_subset_1(C_241, k1_zfmisc_1(k2_zfmisc_1(A_239, B_240))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.84/1.77  tff(c_1181, plain, (k1_relset_1('#skF_7', '#skF_6', '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_58, c_1162])).
% 3.84/1.77  tff(c_1188, plain, (k1_relat_1('#skF_8')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_786, c_1181])).
% 3.84/1.77  tff(c_1190, plain, $false, inference(negUnitSimplification, [status(thm)], [c_827, c_1188])).
% 3.84/1.77  tff(c_1192, plain, (k2_relat_1('#skF_8')=k1_xboole_0), inference(splitRight, [status(thm)], [c_126])).
% 3.84/1.77  tff(c_1552, plain, (![A_301, B_302, C_303]: (k2_relset_1(A_301, B_302, C_303)=k2_relat_1(C_303) | ~m1_subset_1(C_303, k1_zfmisc_1(k2_zfmisc_1(A_301, B_302))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.84/1.77  tff(c_1567, plain, (k2_relset_1('#skF_7', '#skF_6', '#skF_8')=k2_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_58, c_1552])).
% 3.84/1.77  tff(c_1573, plain, (k2_relset_1('#skF_7', '#skF_6', '#skF_8')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1192, c_1567])).
% 3.84/1.77  tff(c_1575, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_1573])).
% 3.84/1.77  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.84/1.77  
% 3.84/1.77  Inference rules
% 3.84/1.77  ----------------------
% 3.84/1.77  #Ref     : 0
% 3.84/1.77  #Sup     : 308
% 3.84/1.77  #Fact    : 0
% 3.84/1.77  #Define  : 0
% 3.84/1.77  #Split   : 10
% 3.84/1.77  #Chain   : 0
% 3.84/1.77  #Close   : 0
% 3.84/1.77  
% 3.84/1.77  Ordering : KBO
% 3.84/1.77  
% 3.84/1.77  Simplification rules
% 3.84/1.77  ----------------------
% 3.84/1.77  #Subsume      : 27
% 3.84/1.77  #Demod        : 104
% 3.84/1.77  #Tautology    : 48
% 3.84/1.77  #SimpNegUnit  : 8
% 3.84/1.77  #BackRed      : 10
% 3.84/1.77  
% 3.84/1.77  #Partial instantiations: 0
% 3.84/1.77  #Strategies tried      : 1
% 3.84/1.77  
% 3.84/1.77  Timing (in seconds)
% 3.84/1.77  ----------------------
% 3.84/1.77  Preprocessing        : 0.35
% 3.84/1.77  Parsing              : 0.18
% 3.84/1.77  CNF conversion       : 0.03
% 3.84/1.77  Main loop            : 0.65
% 3.84/1.77  Inferencing          : 0.26
% 3.84/1.77  Reduction            : 0.18
% 3.84/1.77  Demodulation         : 0.12
% 3.84/1.77  BG Simplification    : 0.03
% 3.84/1.77  Subsumption          : 0.11
% 3.84/1.77  Abstraction          : 0.04
% 3.84/1.77  MUC search           : 0.00
% 3.84/1.77  Cooper               : 0.00
% 3.84/1.77  Total                : 1.04
% 3.84/1.77  Index Insertion      : 0.00
% 3.84/1.77  Index Deletion       : 0.00
% 3.84/1.77  Index Matching       : 0.00
% 3.84/1.77  BG Taut test         : 0.00
%------------------------------------------------------------------------------
