%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0548+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:28 EST 2020

% Result     : Theorem 2.24s
% Output     : CNFRefutation 2.24s
% Verified   : 
% Statistics : Number of formulae       :   40 (  96 expanded)
%              Number of leaves         :   20 (  43 expanded)
%              Depth                    :   12
%              Number of atoms          :   57 ( 165 expanded)
%              Number of equality atoms :   13 (  23 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_xboole_0 > v1_relat_1 > k9_relat_1 > k4_tarski > #nlpp > o_0_0_xboole_0 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_43,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_28,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_41,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( C = k9_relat_1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ? [E] :
                  ( r2_hidden(k4_tarski(E,D),A)
                  & r2_hidden(E,B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_relat_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).

tff(f_55,negated_conjecture,(
    ~ ! [A] : k9_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t150_relat_1)).

tff(c_24,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_47,plain,(
    ! [A_48] :
      ( v1_relat_1(A_48)
      | ~ v1_xboole_0(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_51,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_24,c_47])).

tff(c_302,plain,(
    ! [A_100,B_101,C_102] :
      ( r2_hidden(k4_tarski('#skF_2'(A_100,B_101,C_102),'#skF_1'(A_100,B_101,C_102)),A_100)
      | r2_hidden('#skF_3'(A_100,B_101,C_102),C_102)
      | k9_relat_1(A_100,B_101) = C_102
      | ~ v1_relat_1(A_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_81,plain,(
    ! [A_73,B_74,C_75] :
      ( r2_hidden('#skF_2'(A_73,B_74,C_75),B_74)
      | r2_hidden('#skF_3'(A_73,B_74,C_75),C_75)
      | k9_relat_1(A_73,B_74) = C_75
      | ~ v1_relat_1(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_28,plain,(
    ! [B_46,A_45] :
      ( ~ v1_xboole_0(B_46)
      | ~ r2_hidden(A_45,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_191,plain,(
    ! [C_86,A_87,B_88] :
      ( ~ v1_xboole_0(C_86)
      | r2_hidden('#skF_2'(A_87,B_88,C_86),B_88)
      | k9_relat_1(A_87,B_88) = C_86
      | ~ v1_relat_1(A_87) ) ),
    inference(resolution,[status(thm)],[c_81,c_28])).

tff(c_225,plain,(
    ! [B_93,C_94,A_95] :
      ( ~ v1_xboole_0(B_93)
      | ~ v1_xboole_0(C_94)
      | k9_relat_1(A_95,B_93) = C_94
      | ~ v1_relat_1(A_95) ) ),
    inference(resolution,[status(thm)],[c_191,c_28])).

tff(c_229,plain,(
    ! [C_96,A_97] :
      ( ~ v1_xboole_0(C_96)
      | k9_relat_1(A_97,k1_xboole_0) = C_96
      | ~ v1_relat_1(A_97) ) ),
    inference(resolution,[status(thm)],[c_24,c_225])).

tff(c_233,plain,(
    ! [A_98] :
      ( k9_relat_1(A_98,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_98) ) ),
    inference(resolution,[status(thm)],[c_24,c_229])).

tff(c_237,plain,(
    k9_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_51,c_233])).

tff(c_126,plain,(
    ! [A_76,B_77,D_78] :
      ( r2_hidden(k4_tarski('#skF_4'(A_76,B_77,k9_relat_1(A_76,B_77),D_78),D_78),A_76)
      | ~ r2_hidden(D_78,k9_relat_1(A_76,B_77))
      | ~ v1_relat_1(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_148,plain,(
    ! [A_76,D_78,B_77] :
      ( ~ v1_xboole_0(A_76)
      | ~ r2_hidden(D_78,k9_relat_1(A_76,B_77))
      | ~ v1_relat_1(A_76) ) ),
    inference(resolution,[status(thm)],[c_126,c_28])).

tff(c_244,plain,(
    ! [D_78] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(D_78,k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_237,c_148])).

tff(c_265,plain,(
    ! [D_78] : ~ r2_hidden(D_78,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_24,c_244])).

tff(c_306,plain,(
    ! [B_101,C_102] :
      ( r2_hidden('#skF_3'(k1_xboole_0,B_101,C_102),C_102)
      | k9_relat_1(k1_xboole_0,B_101) = C_102
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_302,c_265])).

tff(c_450,plain,(
    ! [B_114,C_115] :
      ( r2_hidden('#skF_3'(k1_xboole_0,B_114,C_115),C_115)
      | k9_relat_1(k1_xboole_0,B_114) = C_115 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_306])).

tff(c_495,plain,(
    ! [B_114] : k9_relat_1(k1_xboole_0,B_114) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_450,c_265])).

tff(c_30,plain,(
    k9_relat_1(k1_xboole_0,'#skF_5') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_514,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_495,c_30])).

%------------------------------------------------------------------------------
