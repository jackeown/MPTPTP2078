%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:00 EST 2020

% Result     : Theorem 2.31s
% Output     : CNFRefutation 2.73s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 143 expanded)
%              Number of leaves         :   45 (  70 expanded)
%              Depth                    :   13
%              Number of atoms          :  108 ( 260 expanded)
%              Number of equality atoms :   24 (  50 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_7 > #skF_6 > #skF_2 > #skF_9 > #skF_8 > #skF_5 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_61,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_117,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,k1_tarski(A),B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r1_tarski(k7_relset_1(k1_tarski(A),B,D,C),k1_tarski(k1_funct_1(D,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_2)).

tff(f_53,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k9_relat_1(B,A),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_34,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_90,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_105,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_101,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_82,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B,C] :
          ( C = k9_relat_1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ? [E] :
                  ( r2_hidden(E,k1_relat_1(A))
                  & r2_hidden(E,B)
                  & D = k1_funct_1(A,E) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_funct_1)).

tff(f_95,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_28,plain,(
    ! [A_20,B_21] : v1_relat_1(k2_zfmisc_1(A_20,B_21)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_70,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_6'),'#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_98,plain,(
    ! [B_86,A_87] :
      ( v1_relat_1(B_86)
      | ~ m1_subset_1(B_86,k1_zfmisc_1(A_87))
      | ~ v1_relat_1(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_101,plain,
    ( v1_relat_1('#skF_9')
    | ~ v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_6'),'#skF_7')) ),
    inference(resolution,[status(thm)],[c_70,c_98])).

tff(c_104,plain,(
    v1_relat_1('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_101])).

tff(c_30,plain,(
    ! [B_23,A_22] :
      ( r1_tarski(k9_relat_1(B_23,A_22),k2_relat_1(B_23))
      | ~ v1_relat_1(B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_8,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_74,plain,(
    v1_funct_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_266,plain,(
    ! [B_131,A_132] :
      ( k1_tarski(k1_funct_1(B_131,A_132)) = k2_relat_1(B_131)
      | k1_tarski(A_132) != k1_relat_1(B_131)
      | ~ v1_funct_1(B_131)
      | ~ v1_relat_1(B_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_197,plain,(
    ! [A_119,B_120,C_121,D_122] :
      ( k7_relset_1(A_119,B_120,C_121,D_122) = k9_relat_1(C_121,D_122)
      | ~ m1_subset_1(C_121,k1_zfmisc_1(k2_zfmisc_1(A_119,B_120))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_200,plain,(
    ! [D_122] : k7_relset_1(k1_tarski('#skF_6'),'#skF_7','#skF_9',D_122) = k9_relat_1('#skF_9',D_122) ),
    inference(resolution,[status(thm)],[c_70,c_197])).

tff(c_66,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_6'),'#skF_7','#skF_9','#skF_8'),k1_tarski(k1_funct_1('#skF_9','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_201,plain,(
    ~ r1_tarski(k9_relat_1('#skF_9','#skF_8'),k1_tarski(k1_funct_1('#skF_9','#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_200,c_66])).

tff(c_272,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_9','#skF_8'),k2_relat_1('#skF_9'))
    | k1_tarski('#skF_6') != k1_relat_1('#skF_9')
    | ~ v1_funct_1('#skF_9')
    | ~ v1_relat_1('#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_266,c_201])).

tff(c_281,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_9','#skF_8'),k2_relat_1('#skF_9'))
    | k1_tarski('#skF_6') != k1_relat_1('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_74,c_272])).

tff(c_284,plain,(
    k1_tarski('#skF_6') != k1_relat_1('#skF_9') ),
    inference(splitLeft,[status(thm)],[c_281])).

tff(c_131,plain,(
    ! [C_100,A_101,B_102] :
      ( v4_relat_1(C_100,A_101)
      | ~ m1_subset_1(C_100,k1_zfmisc_1(k2_zfmisc_1(A_101,B_102))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_135,plain,(
    v4_relat_1('#skF_9',k1_tarski('#skF_6')) ),
    inference(resolution,[status(thm)],[c_70,c_131])).

tff(c_26,plain,(
    ! [B_19,A_18] :
      ( r1_tarski(k1_relat_1(B_19),A_18)
      | ~ v4_relat_1(B_19,A_18)
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_166,plain,(
    ! [B_114,A_115] :
      ( k1_tarski(B_114) = A_115
      | k1_xboole_0 = A_115
      | ~ r1_tarski(A_115,k1_tarski(B_114)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_313,plain,(
    ! [B_145,B_146] :
      ( k1_tarski(B_145) = k1_relat_1(B_146)
      | k1_relat_1(B_146) = k1_xboole_0
      | ~ v4_relat_1(B_146,k1_tarski(B_145))
      | ~ v1_relat_1(B_146) ) ),
    inference(resolution,[status(thm)],[c_26,c_166])).

tff(c_319,plain,
    ( k1_tarski('#skF_6') = k1_relat_1('#skF_9')
    | k1_relat_1('#skF_9') = k1_xboole_0
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_135,c_313])).

tff(c_322,plain,
    ( k1_tarski('#skF_6') = k1_relat_1('#skF_9')
    | k1_relat_1('#skF_9') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_319])).

tff(c_323,plain,(
    k1_relat_1('#skF_9') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_284,c_322])).

tff(c_395,plain,(
    ! [A_151,B_152,D_153] :
      ( r2_hidden('#skF_5'(A_151,B_152,k9_relat_1(A_151,B_152),D_153),k1_relat_1(A_151))
      | ~ r2_hidden(D_153,k9_relat_1(A_151,B_152))
      | ~ v1_funct_1(A_151)
      | ~ v1_relat_1(A_151) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_403,plain,(
    ! [B_152,D_153] :
      ( r2_hidden('#skF_5'('#skF_9',B_152,k9_relat_1('#skF_9',B_152),D_153),k1_xboole_0)
      | ~ r2_hidden(D_153,k9_relat_1('#skF_9',B_152))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_323,c_395])).

tff(c_432,plain,(
    ! [B_161,D_162] :
      ( r2_hidden('#skF_5'('#skF_9',B_161,k9_relat_1('#skF_9',B_161),D_162),k1_xboole_0)
      | ~ r2_hidden(D_162,k9_relat_1('#skF_9',B_161)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_74,c_403])).

tff(c_58,plain,(
    ! [B_69,A_68] :
      ( ~ r1_tarski(B_69,A_68)
      | ~ r2_hidden(A_68,B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_437,plain,(
    ! [B_161,D_162] :
      ( ~ r1_tarski(k1_xboole_0,'#skF_5'('#skF_9',B_161,k9_relat_1('#skF_9',B_161),D_162))
      | ~ r2_hidden(D_162,k9_relat_1('#skF_9',B_161)) ) ),
    inference(resolution,[status(thm)],[c_432,c_58])).

tff(c_444,plain,(
    ! [D_163,B_164] : ~ r2_hidden(D_163,k9_relat_1('#skF_9',B_164)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_437])).

tff(c_466,plain,(
    ! [B_164,B_2] : r1_tarski(k9_relat_1('#skF_9',B_164),B_2) ),
    inference(resolution,[status(thm)],[c_6,c_444])).

tff(c_469,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_466,c_201])).

tff(c_470,plain,(
    ~ r1_tarski(k9_relat_1('#skF_9','#skF_8'),k2_relat_1('#skF_9')) ),
    inference(splitRight,[status(thm)],[c_281])).

tff(c_513,plain,(
    ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_30,c_470])).

tff(c_517,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_513])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:31:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.31/1.34  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.73/1.34  
% 2.73/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.73/1.34  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_7 > #skF_6 > #skF_2 > #skF_9 > #skF_8 > #skF_5 > #skF_3 > #skF_1
% 2.73/1.34  
% 2.73/1.34  %Foreground sorts:
% 2.73/1.34  
% 2.73/1.34  
% 2.73/1.34  %Background operators:
% 2.73/1.34  
% 2.73/1.34  
% 2.73/1.34  %Foreground operators:
% 2.73/1.34  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.73/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.73/1.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.73/1.34  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.73/1.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.73/1.34  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.73/1.34  tff('#skF_7', type, '#skF_7': $i).
% 2.73/1.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.73/1.34  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.73/1.34  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.73/1.34  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.73/1.34  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.73/1.34  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.73/1.34  tff('#skF_6', type, '#skF_6': $i).
% 2.73/1.34  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.73/1.34  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.73/1.34  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.73/1.34  tff('#skF_9', type, '#skF_9': $i).
% 2.73/1.34  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.73/1.34  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.73/1.34  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.73/1.34  tff('#skF_8', type, '#skF_8': $i).
% 2.73/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.73/1.34  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 2.73/1.34  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.73/1.34  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.73/1.34  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.73/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.73/1.34  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.73/1.34  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.73/1.34  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.73/1.34  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.73/1.34  
% 2.73/1.36  tff(f_61, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.73/1.36  tff(f_117, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, k1_tarski(A), B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r1_tarski(k7_relset_1(k1_tarski(A), B, D, C), k1_tarski(k1_funct_1(D, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_funct_2)).
% 2.73/1.36  tff(f_53, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.73/1.36  tff(f_65, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k2_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t144_relat_1)).
% 2.73/1.36  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.73/1.36  tff(f_34, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.73/1.36  tff(f_90, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_funct_1)).
% 2.73/1.36  tff(f_105, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 2.73/1.36  tff(f_101, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.73/1.36  tff(f_59, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 2.73/1.36  tff(f_46, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 2.73/1.36  tff(f_82, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((C = k9_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: ((r2_hidden(E, k1_relat_1(A)) & r2_hidden(E, B)) & (D = k1_funct_1(A, E)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_funct_1)).
% 2.73/1.36  tff(f_95, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.73/1.36  tff(c_28, plain, (![A_20, B_21]: (v1_relat_1(k2_zfmisc_1(A_20, B_21)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.73/1.36  tff(c_70, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_6'), '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_117])).
% 2.73/1.36  tff(c_98, plain, (![B_86, A_87]: (v1_relat_1(B_86) | ~m1_subset_1(B_86, k1_zfmisc_1(A_87)) | ~v1_relat_1(A_87))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.73/1.36  tff(c_101, plain, (v1_relat_1('#skF_9') | ~v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_6'), '#skF_7'))), inference(resolution, [status(thm)], [c_70, c_98])).
% 2.73/1.36  tff(c_104, plain, (v1_relat_1('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_101])).
% 2.73/1.36  tff(c_30, plain, (![B_23, A_22]: (r1_tarski(k9_relat_1(B_23, A_22), k2_relat_1(B_23)) | ~v1_relat_1(B_23))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.73/1.36  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.73/1.36  tff(c_8, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.73/1.36  tff(c_74, plain, (v1_funct_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_117])).
% 2.73/1.36  tff(c_266, plain, (![B_131, A_132]: (k1_tarski(k1_funct_1(B_131, A_132))=k2_relat_1(B_131) | k1_tarski(A_132)!=k1_relat_1(B_131) | ~v1_funct_1(B_131) | ~v1_relat_1(B_131))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.73/1.36  tff(c_197, plain, (![A_119, B_120, C_121, D_122]: (k7_relset_1(A_119, B_120, C_121, D_122)=k9_relat_1(C_121, D_122) | ~m1_subset_1(C_121, k1_zfmisc_1(k2_zfmisc_1(A_119, B_120))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.73/1.36  tff(c_200, plain, (![D_122]: (k7_relset_1(k1_tarski('#skF_6'), '#skF_7', '#skF_9', D_122)=k9_relat_1('#skF_9', D_122))), inference(resolution, [status(thm)], [c_70, c_197])).
% 2.73/1.36  tff(c_66, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_6'), '#skF_7', '#skF_9', '#skF_8'), k1_tarski(k1_funct_1('#skF_9', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_117])).
% 2.73/1.36  tff(c_201, plain, (~r1_tarski(k9_relat_1('#skF_9', '#skF_8'), k1_tarski(k1_funct_1('#skF_9', '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_200, c_66])).
% 2.73/1.36  tff(c_272, plain, (~r1_tarski(k9_relat_1('#skF_9', '#skF_8'), k2_relat_1('#skF_9')) | k1_tarski('#skF_6')!=k1_relat_1('#skF_9') | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_266, c_201])).
% 2.73/1.36  tff(c_281, plain, (~r1_tarski(k9_relat_1('#skF_9', '#skF_8'), k2_relat_1('#skF_9')) | k1_tarski('#skF_6')!=k1_relat_1('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_104, c_74, c_272])).
% 2.73/1.36  tff(c_284, plain, (k1_tarski('#skF_6')!=k1_relat_1('#skF_9')), inference(splitLeft, [status(thm)], [c_281])).
% 2.73/1.36  tff(c_131, plain, (![C_100, A_101, B_102]: (v4_relat_1(C_100, A_101) | ~m1_subset_1(C_100, k1_zfmisc_1(k2_zfmisc_1(A_101, B_102))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.73/1.36  tff(c_135, plain, (v4_relat_1('#skF_9', k1_tarski('#skF_6'))), inference(resolution, [status(thm)], [c_70, c_131])).
% 2.73/1.36  tff(c_26, plain, (![B_19, A_18]: (r1_tarski(k1_relat_1(B_19), A_18) | ~v4_relat_1(B_19, A_18) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.73/1.36  tff(c_166, plain, (![B_114, A_115]: (k1_tarski(B_114)=A_115 | k1_xboole_0=A_115 | ~r1_tarski(A_115, k1_tarski(B_114)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.73/1.36  tff(c_313, plain, (![B_145, B_146]: (k1_tarski(B_145)=k1_relat_1(B_146) | k1_relat_1(B_146)=k1_xboole_0 | ~v4_relat_1(B_146, k1_tarski(B_145)) | ~v1_relat_1(B_146))), inference(resolution, [status(thm)], [c_26, c_166])).
% 2.73/1.36  tff(c_319, plain, (k1_tarski('#skF_6')=k1_relat_1('#skF_9') | k1_relat_1('#skF_9')=k1_xboole_0 | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_135, c_313])).
% 2.73/1.36  tff(c_322, plain, (k1_tarski('#skF_6')=k1_relat_1('#skF_9') | k1_relat_1('#skF_9')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_104, c_319])).
% 2.73/1.36  tff(c_323, plain, (k1_relat_1('#skF_9')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_284, c_322])).
% 2.73/1.36  tff(c_395, plain, (![A_151, B_152, D_153]: (r2_hidden('#skF_5'(A_151, B_152, k9_relat_1(A_151, B_152), D_153), k1_relat_1(A_151)) | ~r2_hidden(D_153, k9_relat_1(A_151, B_152)) | ~v1_funct_1(A_151) | ~v1_relat_1(A_151))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.73/1.36  tff(c_403, plain, (![B_152, D_153]: (r2_hidden('#skF_5'('#skF_9', B_152, k9_relat_1('#skF_9', B_152), D_153), k1_xboole_0) | ~r2_hidden(D_153, k9_relat_1('#skF_9', B_152)) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_323, c_395])).
% 2.73/1.36  tff(c_432, plain, (![B_161, D_162]: (r2_hidden('#skF_5'('#skF_9', B_161, k9_relat_1('#skF_9', B_161), D_162), k1_xboole_0) | ~r2_hidden(D_162, k9_relat_1('#skF_9', B_161)))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_74, c_403])).
% 2.73/1.36  tff(c_58, plain, (![B_69, A_68]: (~r1_tarski(B_69, A_68) | ~r2_hidden(A_68, B_69))), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.73/1.36  tff(c_437, plain, (![B_161, D_162]: (~r1_tarski(k1_xboole_0, '#skF_5'('#skF_9', B_161, k9_relat_1('#skF_9', B_161), D_162)) | ~r2_hidden(D_162, k9_relat_1('#skF_9', B_161)))), inference(resolution, [status(thm)], [c_432, c_58])).
% 2.73/1.36  tff(c_444, plain, (![D_163, B_164]: (~r2_hidden(D_163, k9_relat_1('#skF_9', B_164)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_437])).
% 2.73/1.36  tff(c_466, plain, (![B_164, B_2]: (r1_tarski(k9_relat_1('#skF_9', B_164), B_2))), inference(resolution, [status(thm)], [c_6, c_444])).
% 2.73/1.36  tff(c_469, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_466, c_201])).
% 2.73/1.36  tff(c_470, plain, (~r1_tarski(k9_relat_1('#skF_9', '#skF_8'), k2_relat_1('#skF_9'))), inference(splitRight, [status(thm)], [c_281])).
% 2.73/1.36  tff(c_513, plain, (~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_30, c_470])).
% 2.73/1.36  tff(c_517, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_104, c_513])).
% 2.73/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.73/1.36  
% 2.73/1.36  Inference rules
% 2.73/1.36  ----------------------
% 2.73/1.36  #Ref     : 0
% 2.73/1.36  #Sup     : 87
% 2.73/1.36  #Fact    : 0
% 2.73/1.36  #Define  : 0
% 2.73/1.36  #Split   : 1
% 2.73/1.36  #Chain   : 0
% 2.73/1.36  #Close   : 0
% 2.73/1.36  
% 2.73/1.36  Ordering : KBO
% 2.73/1.36  
% 2.73/1.36  Simplification rules
% 2.73/1.36  ----------------------
% 2.73/1.36  #Subsume      : 11
% 2.73/1.36  #Demod        : 56
% 2.73/1.36  #Tautology    : 36
% 2.73/1.36  #SimpNegUnit  : 1
% 2.73/1.36  #BackRed      : 7
% 2.73/1.36  
% 2.73/1.36  #Partial instantiations: 0
% 2.73/1.36  #Strategies tried      : 1
% 2.73/1.36  
% 2.73/1.36  Timing (in seconds)
% 2.73/1.36  ----------------------
% 2.73/1.36  Preprocessing        : 0.35
% 2.73/1.36  Parsing              : 0.18
% 2.73/1.36  CNF conversion       : 0.03
% 2.73/1.36  Main loop            : 0.26
% 2.73/1.36  Inferencing          : 0.09
% 2.73/1.36  Reduction            : 0.08
% 2.73/1.36  Demodulation         : 0.06
% 2.73/1.36  BG Simplification    : 0.02
% 2.73/1.36  Subsumption          : 0.05
% 2.73/1.36  Abstraction          : 0.01
% 2.73/1.36  MUC search           : 0.00
% 2.73/1.36  Cooper               : 0.00
% 2.73/1.36  Total                : 0.64
% 2.73/1.37  Index Insertion      : 0.00
% 2.73/1.37  Index Deletion       : 0.00
% 2.73/1.37  Index Matching       : 0.00
% 2.73/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
