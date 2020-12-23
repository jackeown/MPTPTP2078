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
% DateTime   : Thu Dec  3 09:55:17 EST 2020

% Result     : Theorem 5.62s
% Output     : CNFRefutation 5.76s
% Verified   : 
% Statistics : Number of formulae       :  226 (1180 expanded)
%              Number of leaves         :   26 ( 374 expanded)
%              Depth                    :   18
%              Number of atoms          :  412 (3299 expanded)
%              Number of equality atoms :   41 ( 258 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > #nlpp > k3_tarski > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_95,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ( ! [D] :
                  ( m1_subset_1(D,A)
                 => ( r2_hidden(D,B)
                  <=> r2_hidden(D,C) ) )
             => B = C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_subset_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_67,axiom,(
    ! [A] : k3_tarski(k1_zfmisc_1(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_zfmisc_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_zfmisc_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_33,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_61,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

tff(f_48,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k5_xboole_0(B,C))
    <=> ~ ( r2_hidden(A,B)
        <=> r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

tff(c_46,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_42,plain,(
    ! [B_20,A_19] :
      ( m1_subset_1(B_20,A_19)
      | ~ v1_xboole_0(B_20)
      | ~ v1_xboole_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_40,plain,(
    ! [B_20,A_19] :
      ( r2_hidden(B_20,A_19)
      | ~ m1_subset_1(B_20,A_19)
      | v1_xboole_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_122,plain,(
    ! [D_45] :
      ( r2_hidden(D_45,'#skF_3')
      | ~ r2_hidden(D_45,'#skF_4')
      | ~ m1_subset_1(D_45,'#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_30,plain,(
    ! [B_13,A_12] :
      ( ~ v1_xboole_0(B_13)
      | ~ r2_hidden(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_130,plain,(
    ! [D_45] :
      ( ~ v1_xboole_0('#skF_3')
      | ~ r2_hidden(D_45,'#skF_4')
      | ~ m1_subset_1(D_45,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_122,c_30])).

tff(c_214,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_130])).

tff(c_140,plain,(
    ! [A_48,B_49] :
      ( r2_hidden('#skF_1'(A_48,B_49),A_48)
      | r1_tarski(A_48,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_38,plain,(
    ! [B_20,A_19] :
      ( m1_subset_1(B_20,A_19)
      | ~ r2_hidden(B_20,A_19)
      | v1_xboole_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_155,plain,(
    ! [A_48,B_49] :
      ( m1_subset_1('#skF_1'(A_48,B_49),A_48)
      | v1_xboole_0(A_48)
      | r1_tarski(A_48,B_49) ) ),
    inference(resolution,[status(thm)],[c_140,c_38])).

tff(c_107,plain,(
    ! [B_43,A_44] :
      ( r2_hidden(B_43,A_44)
      | ~ m1_subset_1(B_43,A_44)
      | v1_xboole_0(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_54,plain,(
    ! [D_25] :
      ( r2_hidden(D_25,'#skF_4')
      | ~ r2_hidden(D_25,'#skF_3')
      | ~ m1_subset_1(D_25,'#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_120,plain,(
    ! [B_43] :
      ( r2_hidden(B_43,'#skF_4')
      | ~ m1_subset_1(B_43,'#skF_2')
      | ~ m1_subset_1(B_43,'#skF_3')
      | v1_xboole_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_107,c_54])).

tff(c_216,plain,(
    ! [B_61] :
      ( r2_hidden(B_61,'#skF_4')
      | ~ m1_subset_1(B_61,'#skF_2')
      | ~ m1_subset_1(B_61,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_214,c_120])).

tff(c_232,plain,(
    ! [B_61] :
      ( ~ v1_xboole_0('#skF_4')
      | ~ m1_subset_1(B_61,'#skF_2')
      | ~ m1_subset_1(B_61,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_216,c_30])).

tff(c_233,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_232])).

tff(c_48,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_87,plain,(
    ! [B_35,A_36] :
      ( v1_xboole_0(B_35)
      | ~ m1_subset_1(B_35,A_36)
      | ~ v1_xboole_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_94,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0(k1_zfmisc_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_48,c_87])).

tff(c_96,plain,(
    ~ v1_xboole_0(k1_zfmisc_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_94])).

tff(c_36,plain,(
    ! [A_18] : k3_tarski(k1_zfmisc_1(A_18)) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_102,plain,(
    ! [A_39,B_40] :
      ( r1_tarski(A_39,k3_tarski(B_40))
      | ~ r2_hidden(A_39,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_105,plain,(
    ! [A_39,A_18] :
      ( r1_tarski(A_39,A_18)
      | ~ r2_hidden(A_39,k1_zfmisc_1(A_18)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_102])).

tff(c_358,plain,(
    ! [B_84,A_85] :
      ( r1_tarski(B_84,A_85)
      | ~ m1_subset_1(B_84,k1_zfmisc_1(A_85))
      | v1_xboole_0(k1_zfmisc_1(A_85)) ) ),
    inference(resolution,[status(thm)],[c_107,c_105])).

tff(c_369,plain,
    ( r1_tarski('#skF_4','#skF_2')
    | v1_xboole_0(k1_zfmisc_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_48,c_358])).

tff(c_377,plain,(
    r1_tarski('#skF_4','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_369])).

tff(c_158,plain,(
    ! [A_48,B_49] :
      ( ~ v1_xboole_0(A_48)
      | r1_tarski(A_48,B_49) ) ),
    inference(resolution,[status(thm)],[c_140,c_30])).

tff(c_177,plain,(
    ! [B_54,A_55] :
      ( B_54 = A_55
      | ~ r1_tarski(B_54,A_55)
      | ~ r1_tarski(A_55,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_184,plain,(
    ! [B_49,A_48] :
      ( B_49 = A_48
      | ~ r1_tarski(B_49,A_48)
      | ~ v1_xboole_0(A_48) ) ),
    inference(resolution,[status(thm)],[c_158,c_177])).

tff(c_386,plain,
    ( '#skF_2' = '#skF_4'
    | ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_377,c_184])).

tff(c_415,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_386])).

tff(c_50,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_372,plain,
    ( r1_tarski('#skF_3','#skF_2')
    | v1_xboole_0(k1_zfmisc_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_50,c_358])).

tff(c_380,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_372])).

tff(c_190,plain,(
    ! [C_56,B_57,A_58] :
      ( r2_hidden(C_56,B_57)
      | ~ r2_hidden(C_56,A_58)
      | ~ r1_tarski(A_58,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1057,plain,(
    ! [B_125,B_126,A_127] :
      ( r2_hidden(B_125,B_126)
      | ~ r1_tarski(A_127,B_126)
      | ~ m1_subset_1(B_125,A_127)
      | v1_xboole_0(A_127) ) ),
    inference(resolution,[status(thm)],[c_40,c_190])).

tff(c_1061,plain,(
    ! [B_125] :
      ( r2_hidden(B_125,'#skF_2')
      | ~ m1_subset_1(B_125,'#skF_3')
      | v1_xboole_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_380,c_1057])).

tff(c_1084,plain,(
    ! [B_128] :
      ( r2_hidden(B_128,'#skF_2')
      | ~ m1_subset_1(B_128,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_214,c_1061])).

tff(c_1093,plain,(
    ! [B_128] :
      ( m1_subset_1(B_128,'#skF_2')
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(B_128,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_1084,c_38])).

tff(c_1122,plain,(
    ! [B_130] :
      ( m1_subset_1(B_130,'#skF_2')
      | ~ m1_subset_1(B_130,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_415,c_1093])).

tff(c_629,plain,(
    ! [B_107] :
      ( r2_hidden('#skF_1'('#skF_3',B_107),'#skF_4')
      | ~ m1_subset_1('#skF_1'('#skF_3',B_107),'#skF_2')
      | r1_tarski('#skF_3',B_107) ) ),
    inference(resolution,[status(thm)],[c_140,c_54])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_656,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_3','#skF_4'),'#skF_2')
    | r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_629,c_4])).

tff(c_661,plain,(
    ~ m1_subset_1('#skF_1'('#skF_3','#skF_4'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_656])).

tff(c_1139,plain,(
    ~ m1_subset_1('#skF_1'('#skF_3','#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_1122,c_661])).

tff(c_1163,plain,
    ( v1_xboole_0('#skF_3')
    | r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_155,c_1139])).

tff(c_1169,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_214,c_1163])).

tff(c_22,plain,(
    ! [B_10,A_9] :
      ( B_10 = A_9
      | ~ r1_tarski(B_10,A_9)
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1179,plain,
    ( '#skF_3' = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_1169,c_22])).

tff(c_1188,plain,(
    ~ r1_tarski('#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_1179])).

tff(c_1063,plain,(
    ! [B_125] :
      ( r2_hidden(B_125,'#skF_2')
      | ~ m1_subset_1(B_125,'#skF_4')
      | v1_xboole_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_377,c_1057])).

tff(c_1103,plain,(
    ! [B_129] :
      ( r2_hidden(B_129,'#skF_2')
      | ~ m1_subset_1(B_129,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_233,c_1063])).

tff(c_1112,plain,(
    ! [B_129] :
      ( m1_subset_1(B_129,'#skF_2')
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(B_129,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1103,c_38])).

tff(c_1197,plain,(
    ! [B_132] :
      ( m1_subset_1(B_132,'#skF_2')
      | ~ m1_subset_1(B_132,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_415,c_1112])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_52,plain,(
    ! [D_25] :
      ( r2_hidden(D_25,'#skF_3')
      | ~ r2_hidden(D_25,'#skF_4')
      | ~ m1_subset_1(D_25,'#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_160,plain,(
    ! [A_52,B_53] :
      ( ~ r2_hidden('#skF_1'(A_52,B_53),B_53)
      | r1_tarski(A_52,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_536,plain,(
    ! [A_99] :
      ( r1_tarski(A_99,'#skF_3')
      | ~ r2_hidden('#skF_1'(A_99,'#skF_3'),'#skF_4')
      | ~ m1_subset_1('#skF_1'(A_99,'#skF_3'),'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_52,c_160])).

tff(c_548,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_4','#skF_3'),'#skF_2')
    | r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_6,c_536])).

tff(c_576,plain,(
    ~ m1_subset_1('#skF_1'('#skF_4','#skF_3'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_548])).

tff(c_1219,plain,(
    ~ m1_subset_1('#skF_1'('#skF_4','#skF_3'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_1197,c_576])).

tff(c_1246,plain,
    ( v1_xboole_0('#skF_4')
    | r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_155,c_1219])).

tff(c_1253,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1188,c_233,c_1246])).

tff(c_1254,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_656])).

tff(c_1260,plain,
    ( '#skF_3' = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_1254,c_22])).

tff(c_1265,plain,(
    ~ r1_tarski('#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_1260])).

tff(c_1492,plain,(
    ! [B_144,B_145,A_146] :
      ( r2_hidden(B_144,B_145)
      | ~ r1_tarski(A_146,B_145)
      | ~ m1_subset_1(B_144,A_146)
      | v1_xboole_0(A_146) ) ),
    inference(resolution,[status(thm)],[c_40,c_190])).

tff(c_1500,plain,(
    ! [B_144] :
      ( r2_hidden(B_144,'#skF_2')
      | ~ m1_subset_1(B_144,'#skF_4')
      | v1_xboole_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_377,c_1492])).

tff(c_1588,plain,(
    ! [B_150] :
      ( r2_hidden(B_150,'#skF_2')
      | ~ m1_subset_1(B_150,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_233,c_1500])).

tff(c_1597,plain,(
    ! [B_150] :
      ( m1_subset_1(B_150,'#skF_2')
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(B_150,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1588,c_38])).

tff(c_1786,plain,(
    ! [B_159] :
      ( m1_subset_1(B_159,'#skF_2')
      | ~ m1_subset_1(B_159,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_415,c_1597])).

tff(c_1804,plain,(
    ~ m1_subset_1('#skF_1'('#skF_4','#skF_3'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_1786,c_576])).

tff(c_1812,plain,
    ( v1_xboole_0('#skF_4')
    | r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_155,c_1804])).

tff(c_1819,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1265,c_233,c_1812])).

tff(c_1820,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_548])).

tff(c_1826,plain,
    ( '#skF_3' = '#skF_4'
    | ~ r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_1820,c_22])).

tff(c_1831,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_1826])).

tff(c_2117,plain,(
    ! [B_174,B_175,A_176] :
      ( r2_hidden(B_174,B_175)
      | ~ r1_tarski(A_176,B_175)
      | ~ m1_subset_1(B_174,A_176)
      | v1_xboole_0(A_176) ) ),
    inference(resolution,[status(thm)],[c_40,c_190])).

tff(c_2123,plain,(
    ! [B_174] :
      ( r2_hidden(B_174,'#skF_2')
      | ~ m1_subset_1(B_174,'#skF_3')
      | v1_xboole_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_380,c_2117])).

tff(c_2334,plain,(
    ! [B_184] :
      ( r2_hidden(B_184,'#skF_2')
      | ~ m1_subset_1(B_184,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_214,c_2123])).

tff(c_2343,plain,(
    ! [B_184] :
      ( m1_subset_1(B_184,'#skF_2')
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(B_184,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_2334,c_38])).

tff(c_2403,plain,(
    ! [B_187] :
      ( m1_subset_1(B_187,'#skF_2')
      | ~ m1_subset_1(B_187,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_415,c_2343])).

tff(c_1879,plain,(
    ! [B_165] :
      ( r2_hidden('#skF_1'('#skF_3',B_165),'#skF_4')
      | ~ m1_subset_1('#skF_1'('#skF_3',B_165),'#skF_2')
      | r1_tarski('#skF_3',B_165) ) ),
    inference(resolution,[status(thm)],[c_140,c_54])).

tff(c_1894,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_3','#skF_4'),'#skF_2')
    | r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_1879,c_4])).

tff(c_1908,plain,(
    ~ m1_subset_1('#skF_1'('#skF_3','#skF_4'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_1831,c_1831,c_1894])).

tff(c_2418,plain,(
    ~ m1_subset_1('#skF_1'('#skF_3','#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_2403,c_1908])).

tff(c_2428,plain,
    ( v1_xboole_0('#skF_3')
    | r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_155,c_2418])).

tff(c_2436,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1831,c_214,c_2428])).

tff(c_2437,plain,(
    '#skF_2' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_386])).

tff(c_2438,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_386])).

tff(c_2454,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2437,c_2438])).

tff(c_2455,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_233,c_2454])).

tff(c_2522,plain,(
    ! [B_194] :
      ( ~ m1_subset_1(B_194,'#skF_2')
      | ~ m1_subset_1(B_194,'#skF_3') ) ),
    inference(splitRight,[status(thm)],[c_232])).

tff(c_2527,plain,(
    ! [B_20] :
      ( ~ m1_subset_1(B_20,'#skF_3')
      | ~ v1_xboole_0(B_20)
      | ~ v1_xboole_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_42,c_2522])).

tff(c_2528,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_2527])).

tff(c_3280,plain,(
    ! [B_267,A_268] :
      ( r1_tarski(B_267,A_268)
      | ~ m1_subset_1(B_267,k1_zfmisc_1(A_268))
      | v1_xboole_0(k1_zfmisc_1(A_268)) ) ),
    inference(resolution,[status(thm)],[c_107,c_105])).

tff(c_3297,plain,
    ( r1_tarski('#skF_3','#skF_2')
    | v1_xboole_0(k1_zfmisc_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_50,c_3280])).

tff(c_3306,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_3297])).

tff(c_199,plain,(
    ! [B_20,B_57,A_19] :
      ( r2_hidden(B_20,B_57)
      | ~ r1_tarski(A_19,B_57)
      | ~ m1_subset_1(B_20,A_19)
      | v1_xboole_0(A_19) ) ),
    inference(resolution,[status(thm)],[c_40,c_190])).

tff(c_3310,plain,(
    ! [B_20] :
      ( r2_hidden(B_20,'#skF_2')
      | ~ m1_subset_1(B_20,'#skF_3')
      | v1_xboole_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_3306,c_199])).

tff(c_3342,plain,(
    ! [B_273] :
      ( r2_hidden(B_273,'#skF_2')
      | ~ m1_subset_1(B_273,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_214,c_3310])).

tff(c_3351,plain,(
    ! [B_273] :
      ( m1_subset_1(B_273,'#skF_2')
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(B_273,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_3342,c_38])).

tff(c_3361,plain,(
    ! [B_274] :
      ( m1_subset_1(B_274,'#skF_2')
      | ~ m1_subset_1(B_274,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_2528,c_3351])).

tff(c_2456,plain,(
    ! [B_61] :
      ( ~ m1_subset_1(B_61,'#skF_2')
      | ~ m1_subset_1(B_61,'#skF_3') ) ),
    inference(splitRight,[status(thm)],[c_232])).

tff(c_3410,plain,(
    ! [B_276] : ~ m1_subset_1(B_276,'#skF_3') ),
    inference(resolution,[status(thm)],[c_3361,c_2456])).

tff(c_3414,plain,(
    ! [B_49] :
      ( v1_xboole_0('#skF_3')
      | r1_tarski('#skF_3',B_49) ) ),
    inference(resolution,[status(thm)],[c_155,c_3410])).

tff(c_3427,plain,(
    ! [B_277] : r1_tarski('#skF_3',B_277) ),
    inference(negUnitSimplification,[status(thm)],[c_214,c_3414])).

tff(c_2457,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_232])).

tff(c_8,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_76,plain,(
    ! [B_31,A_32] :
      ( ~ v1_xboole_0(B_31)
      | B_31 = A_32
      | ~ v1_xboole_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_79,plain,(
    ! [A_32] :
      ( k1_xboole_0 = A_32
      | ~ v1_xboole_0(A_32) ) ),
    inference(resolution,[status(thm)],[c_8,c_76])).

tff(c_2463,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_2457,c_79])).

tff(c_28,plain,(
    ! [A_11] : k5_xboole_0(A_11,k1_xboole_0) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_2480,plain,(
    ! [A_11] : k5_xboole_0(A_11,'#skF_4') = A_11 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2463,c_28])).

tff(c_2533,plain,(
    ! [A_197,B_198,C_199] :
      ( r2_hidden(A_197,B_198)
      | ~ r2_hidden(A_197,C_199)
      | r2_hidden(A_197,k5_xboole_0(B_198,C_199)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_2568,plain,(
    ! [A_202,A_203] :
      ( r2_hidden(A_202,A_203)
      | ~ r2_hidden(A_202,'#skF_4')
      | r2_hidden(A_202,A_203) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2480,c_2533])).

tff(c_2578,plain,(
    ! [B_204,A_205] :
      ( r2_hidden('#skF_1'('#skF_4',B_204),A_205)
      | r1_tarski('#skF_4',B_204) ) ),
    inference(resolution,[status(thm)],[c_6,c_2568])).

tff(c_2639,plain,(
    ! [A_208] : r1_tarski('#skF_4',A_208) ),
    inference(resolution,[status(thm)],[c_2578,c_4])).

tff(c_2646,plain,(
    ! [A_208] :
      ( A_208 = '#skF_4'
      | ~ r1_tarski(A_208,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_2639,c_22])).

tff(c_3435,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_3427,c_2646])).

tff(c_3448,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_3435])).

tff(c_3450,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_2527])).

tff(c_32,plain,(
    ! [B_15,A_14] :
      ( ~ v1_xboole_0(B_15)
      | B_15 = A_14
      | ~ v1_xboole_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_2464,plain,(
    ! [A_14] :
      ( A_14 = '#skF_4'
      | ~ v1_xboole_0(A_14) ) ),
    inference(resolution,[status(thm)],[c_2457,c_32])).

tff(c_3456,plain,(
    '#skF_2' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_3450,c_2464])).

tff(c_3462,plain,(
    ~ v1_xboole_0(k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3456,c_96])).

tff(c_3465,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3456,c_50])).

tff(c_4238,plain,(
    ! [B_347,A_348] :
      ( r1_tarski(B_347,A_348)
      | ~ m1_subset_1(B_347,k1_zfmisc_1(A_348))
      | v1_xboole_0(k1_zfmisc_1(A_348)) ) ),
    inference(resolution,[status(thm)],[c_107,c_105])).

tff(c_4248,plain,
    ( r1_tarski('#skF_3','#skF_4')
    | v1_xboole_0(k1_zfmisc_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_3465,c_4238])).

tff(c_4259,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_3462,c_4248])).

tff(c_3568,plain,(
    ! [A_289,B_290,C_291] :
      ( r2_hidden(A_289,B_290)
      | ~ r2_hidden(A_289,C_291)
      | r2_hidden(A_289,k5_xboole_0(B_290,C_291)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_3604,plain,(
    ! [A_293,A_294] :
      ( r2_hidden(A_293,A_294)
      | ~ r2_hidden(A_293,'#skF_4')
      | r2_hidden(A_293,A_294) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2480,c_3568])).

tff(c_3614,plain,(
    ! [B_295,A_296] :
      ( r2_hidden('#skF_1'('#skF_4',B_295),A_296)
      | r1_tarski('#skF_4',B_295) ) ),
    inference(resolution,[status(thm)],[c_6,c_3604])).

tff(c_3676,plain,(
    ! [A_299] : r1_tarski('#skF_4',A_299) ),
    inference(resolution,[status(thm)],[c_3614,c_4])).

tff(c_3683,plain,(
    ! [A_299] :
      ( A_299 = '#skF_4'
      | ~ r1_tarski(A_299,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_3676,c_22])).

tff(c_4282,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_4259,c_3683])).

tff(c_4297,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_4282])).

tff(c_4331,plain,(
    ! [D_355] :
      ( ~ r2_hidden(D_355,'#skF_4')
      | ~ m1_subset_1(D_355,'#skF_2') ) ),
    inference(splitRight,[status(thm)],[c_130])).

tff(c_4341,plain,(
    ! [B_20] :
      ( ~ m1_subset_1(B_20,'#skF_2')
      | ~ m1_subset_1(B_20,'#skF_4')
      | v1_xboole_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_40,c_4331])).

tff(c_4362,plain,(
    ! [B_360] :
      ( ~ m1_subset_1(B_360,'#skF_2')
      | ~ m1_subset_1(B_360,'#skF_4') ) ),
    inference(splitLeft,[status(thm)],[c_4341])).

tff(c_4367,plain,(
    ! [B_20] :
      ( ~ m1_subset_1(B_20,'#skF_4')
      | ~ v1_xboole_0(B_20)
      | ~ v1_xboole_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_42,c_4362])).

tff(c_4368,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_4367])).

tff(c_4441,plain,(
    ! [A_372,B_373] :
      ( m1_subset_1('#skF_1'(A_372,B_373),A_372)
      | v1_xboole_0(A_372)
      | r1_tarski(A_372,B_373) ) ),
    inference(resolution,[status(thm)],[c_140,c_38])).

tff(c_4361,plain,(
    ! [B_20] :
      ( ~ m1_subset_1(B_20,'#skF_2')
      | ~ m1_subset_1(B_20,'#skF_4') ) ),
    inference(splitLeft,[status(thm)],[c_4341])).

tff(c_4445,plain,(
    ! [B_373] :
      ( ~ m1_subset_1('#skF_1'('#skF_2',B_373),'#skF_4')
      | v1_xboole_0('#skF_2')
      | r1_tarski('#skF_2',B_373) ) ),
    inference(resolution,[status(thm)],[c_4441,c_4361])).

tff(c_4453,plain,(
    ! [B_374] :
      ( ~ m1_subset_1('#skF_1'('#skF_2',B_374),'#skF_4')
      | r1_tarski('#skF_2',B_374) ) ),
    inference(negUnitSimplification,[status(thm)],[c_4368,c_4445])).

tff(c_4457,plain,(
    ! [B_374] :
      ( r1_tarski('#skF_2',B_374)
      | ~ v1_xboole_0('#skF_1'('#skF_2',B_374))
      | ~ v1_xboole_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_42,c_4453])).

tff(c_4458,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_4457])).

tff(c_4819,plain,(
    ! [B_407,A_408] :
      ( r1_tarski(B_407,A_408)
      | ~ m1_subset_1(B_407,k1_zfmisc_1(A_408))
      | v1_xboole_0(k1_zfmisc_1(A_408)) ) ),
    inference(resolution,[status(thm)],[c_107,c_105])).

tff(c_4833,plain,
    ( r1_tarski('#skF_4','#skF_2')
    | v1_xboole_0(k1_zfmisc_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_48,c_4819])).

tff(c_4842,plain,(
    r1_tarski('#skF_4','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_4833])).

tff(c_4847,plain,(
    ! [B_20] :
      ( r2_hidden(B_20,'#skF_2')
      | ~ m1_subset_1(B_20,'#skF_4')
      | v1_xboole_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_4842,c_199])).

tff(c_4863,plain,(
    ! [B_409] :
      ( r2_hidden(B_409,'#skF_2')
      | ~ m1_subset_1(B_409,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_4458,c_4847])).

tff(c_4872,plain,(
    ! [B_409] :
      ( m1_subset_1(B_409,'#skF_2')
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(B_409,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_4863,c_38])).

tff(c_4882,plain,(
    ! [B_410] :
      ( m1_subset_1(B_410,'#skF_2')
      | ~ m1_subset_1(B_410,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_4368,c_4872])).

tff(c_4981,plain,(
    ! [B_414] : ~ m1_subset_1(B_414,'#skF_4') ),
    inference(resolution,[status(thm)],[c_4882,c_4361])).

tff(c_4985,plain,(
    ! [B_49] :
      ( v1_xboole_0('#skF_4')
      | r1_tarski('#skF_4',B_49) ) ),
    inference(resolution,[status(thm)],[c_155,c_4981])).

tff(c_4996,plain,(
    ! [B_415] : r1_tarski('#skF_4',B_415) ),
    inference(negUnitSimplification,[status(thm)],[c_4458,c_4985])).

tff(c_4299,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_130])).

tff(c_4305,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_4299,c_79])).

tff(c_4308,plain,(
    ! [A_11] : k5_xboole_0(A_11,'#skF_3') = A_11 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4305,c_28])).

tff(c_4482,plain,(
    ! [A_382,B_383,C_384] :
      ( r2_hidden(A_382,B_383)
      | ~ r2_hidden(A_382,C_384)
      | r2_hidden(A_382,k5_xboole_0(B_383,C_384)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_4506,plain,(
    ! [A_385,A_386] :
      ( r2_hidden(A_385,A_386)
      | ~ r2_hidden(A_385,'#skF_3')
      | r2_hidden(A_385,A_386) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4308,c_4482])).

tff(c_4516,plain,(
    ! [B_387,A_388] :
      ( r2_hidden('#skF_1'('#skF_3',B_387),A_388)
      | r1_tarski('#skF_3',B_387) ) ),
    inference(resolution,[status(thm)],[c_6,c_4506])).

tff(c_4568,plain,(
    ! [A_389] : r1_tarski('#skF_3',A_389) ),
    inference(resolution,[status(thm)],[c_4516,c_4])).

tff(c_4575,plain,(
    ! [A_389] :
      ( A_389 = '#skF_3'
      | ~ r1_tarski(A_389,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_4568,c_22])).

tff(c_5002,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_4996,c_4575])).

tff(c_5013,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_5002])).

tff(c_5015,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_4457])).

tff(c_4306,plain,(
    ! [A_14] :
      ( A_14 = '#skF_3'
      | ~ v1_xboole_0(A_14) ) ),
    inference(resolution,[status(thm)],[c_4299,c_32])).

tff(c_5018,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_5015,c_4306])).

tff(c_5024,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_5018])).

tff(c_5026,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_4367])).

tff(c_5033,plain,(
    '#skF_2' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_5026,c_4306])).

tff(c_5039,plain,(
    ~ v1_xboole_0(k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5033,c_96])).

tff(c_5041,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5033,c_48])).

tff(c_5743,plain,(
    ! [B_482,A_483] :
      ( r1_tarski(B_482,A_483)
      | ~ m1_subset_1(B_482,k1_zfmisc_1(A_483))
      | v1_xboole_0(k1_zfmisc_1(A_483)) ) ),
    inference(resolution,[status(thm)],[c_107,c_105])).

tff(c_5753,plain,
    ( r1_tarski('#skF_4','#skF_3')
    | v1_xboole_0(k1_zfmisc_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_5041,c_5743])).

tff(c_5764,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_5039,c_5753])).

tff(c_5053,plain,(
    ! [A_416,B_417,C_418] :
      ( r2_hidden(A_416,B_417)
      | ~ r2_hidden(A_416,C_418)
      | r2_hidden(A_416,k5_xboole_0(B_417,C_418)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_5170,plain,(
    ! [A_432,A_433] :
      ( r2_hidden(A_432,A_433)
      | ~ r2_hidden(A_432,'#skF_3')
      | r2_hidden(A_432,A_433) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4308,c_5053])).

tff(c_5180,plain,(
    ! [B_434,A_435] :
      ( r2_hidden('#skF_1'('#skF_3',B_434),A_435)
      | r1_tarski('#skF_3',B_434) ) ),
    inference(resolution,[status(thm)],[c_6,c_5170])).

tff(c_5227,plain,(
    ! [A_436] : r1_tarski('#skF_3',A_436) ),
    inference(resolution,[status(thm)],[c_5180,c_4])).

tff(c_5234,plain,(
    ! [A_436] :
      ( A_436 = '#skF_3'
      | ~ r1_tarski(A_436,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_5227,c_22])).

tff(c_5772,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_5764,c_5234])).

tff(c_5787,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_5772])).

tff(c_5788,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_4341])).

tff(c_5791,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_5788,c_4306])).

tff(c_5797,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_5791])).

tff(c_5798,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_94])).

tff(c_5799,plain,(
    v1_xboole_0(k1_zfmisc_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_94])).

tff(c_5832,plain,(
    ! [A_487] :
      ( A_487 = '#skF_4'
      | ~ v1_xboole_0(A_487) ) ),
    inference(resolution,[status(thm)],[c_5798,c_32])).

tff(c_5839,plain,(
    k1_zfmisc_1('#skF_2') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_5799,c_5832])).

tff(c_5844,plain,(
    m1_subset_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5839,c_50])).

tff(c_44,plain,(
    ! [B_20,A_19] :
      ( v1_xboole_0(B_20)
      | ~ m1_subset_1(B_20,A_19)
      | ~ v1_xboole_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_5861,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_5844,c_44])).

tff(c_5864,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5798,c_5861])).

tff(c_5811,plain,(
    ! [A_14] :
      ( A_14 = '#skF_4'
      | ~ v1_xboole_0(A_14) ) ),
    inference(resolution,[status(thm)],[c_5798,c_32])).

tff(c_5867,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_5864,c_5811])).

tff(c_5873,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_5867])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:28:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.62/2.05  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.62/2.08  
% 5.62/2.08  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.62/2.08  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > #nlpp > k3_tarski > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 5.62/2.08  
% 5.62/2.08  %Foreground sorts:
% 5.62/2.08  
% 5.62/2.08  
% 5.62/2.08  %Background operators:
% 5.62/2.08  
% 5.62/2.08  
% 5.62/2.08  %Foreground operators:
% 5.62/2.08  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.62/2.08  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.62/2.08  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.62/2.08  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.62/2.08  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.62/2.08  tff('#skF_2', type, '#skF_2': $i).
% 5.62/2.08  tff('#skF_3', type, '#skF_3': $i).
% 5.62/2.08  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.62/2.08  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.62/2.08  tff(k3_tarski, type, k3_tarski: $i > $i).
% 5.62/2.08  tff('#skF_4', type, '#skF_4': $i).
% 5.62/2.08  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.62/2.08  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.62/2.08  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.62/2.08  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.62/2.08  
% 5.76/2.11  tff(f_95, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((![D]: (m1_subset_1(D, A) => (r2_hidden(D, B) <=> r2_hidden(D, C)))) => (B = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_subset_1)).
% 5.76/2.11  tff(f_80, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 5.76/2.11  tff(f_53, axiom, (![A, B]: ~(r2_hidden(A, B) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_boole)).
% 5.76/2.11  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 5.76/2.11  tff(f_67, axiom, (![A]: (k3_tarski(k1_zfmisc_1(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 5.76/2.11  tff(f_65, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_zfmisc_1)).
% 5.76/2.11  tff(f_46, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.76/2.11  tff(f_33, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 5.76/2.11  tff(f_61, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 5.76/2.11  tff(f_48, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 5.76/2.11  tff(f_40, axiom, (![A, B, C]: (r2_hidden(A, k5_xboole_0(B, C)) <=> ~(r2_hidden(A, B) <=> r2_hidden(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_0)).
% 5.76/2.11  tff(c_46, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_95])).
% 5.76/2.11  tff(c_42, plain, (![B_20, A_19]: (m1_subset_1(B_20, A_19) | ~v1_xboole_0(B_20) | ~v1_xboole_0(A_19))), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.76/2.11  tff(c_40, plain, (![B_20, A_19]: (r2_hidden(B_20, A_19) | ~m1_subset_1(B_20, A_19) | v1_xboole_0(A_19))), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.76/2.11  tff(c_122, plain, (![D_45]: (r2_hidden(D_45, '#skF_3') | ~r2_hidden(D_45, '#skF_4') | ~m1_subset_1(D_45, '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_95])).
% 5.76/2.11  tff(c_30, plain, (![B_13, A_12]: (~v1_xboole_0(B_13) | ~r2_hidden(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.76/2.11  tff(c_130, plain, (![D_45]: (~v1_xboole_0('#skF_3') | ~r2_hidden(D_45, '#skF_4') | ~m1_subset_1(D_45, '#skF_2'))), inference(resolution, [status(thm)], [c_122, c_30])).
% 5.76/2.11  tff(c_214, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_130])).
% 5.76/2.11  tff(c_140, plain, (![A_48, B_49]: (r2_hidden('#skF_1'(A_48, B_49), A_48) | r1_tarski(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.76/2.11  tff(c_38, plain, (![B_20, A_19]: (m1_subset_1(B_20, A_19) | ~r2_hidden(B_20, A_19) | v1_xboole_0(A_19))), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.76/2.11  tff(c_155, plain, (![A_48, B_49]: (m1_subset_1('#skF_1'(A_48, B_49), A_48) | v1_xboole_0(A_48) | r1_tarski(A_48, B_49))), inference(resolution, [status(thm)], [c_140, c_38])).
% 5.76/2.11  tff(c_107, plain, (![B_43, A_44]: (r2_hidden(B_43, A_44) | ~m1_subset_1(B_43, A_44) | v1_xboole_0(A_44))), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.76/2.11  tff(c_54, plain, (![D_25]: (r2_hidden(D_25, '#skF_4') | ~r2_hidden(D_25, '#skF_3') | ~m1_subset_1(D_25, '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_95])).
% 5.76/2.11  tff(c_120, plain, (![B_43]: (r2_hidden(B_43, '#skF_4') | ~m1_subset_1(B_43, '#skF_2') | ~m1_subset_1(B_43, '#skF_3') | v1_xboole_0('#skF_3'))), inference(resolution, [status(thm)], [c_107, c_54])).
% 5.76/2.11  tff(c_216, plain, (![B_61]: (r2_hidden(B_61, '#skF_4') | ~m1_subset_1(B_61, '#skF_2') | ~m1_subset_1(B_61, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_214, c_120])).
% 5.76/2.11  tff(c_232, plain, (![B_61]: (~v1_xboole_0('#skF_4') | ~m1_subset_1(B_61, '#skF_2') | ~m1_subset_1(B_61, '#skF_3'))), inference(resolution, [status(thm)], [c_216, c_30])).
% 5.76/2.11  tff(c_233, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_232])).
% 5.76/2.11  tff(c_48, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_95])).
% 5.76/2.11  tff(c_87, plain, (![B_35, A_36]: (v1_xboole_0(B_35) | ~m1_subset_1(B_35, A_36) | ~v1_xboole_0(A_36))), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.76/2.11  tff(c_94, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0(k1_zfmisc_1('#skF_2'))), inference(resolution, [status(thm)], [c_48, c_87])).
% 5.76/2.11  tff(c_96, plain, (~v1_xboole_0(k1_zfmisc_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_94])).
% 5.76/2.11  tff(c_36, plain, (![A_18]: (k3_tarski(k1_zfmisc_1(A_18))=A_18)), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.76/2.11  tff(c_102, plain, (![A_39, B_40]: (r1_tarski(A_39, k3_tarski(B_40)) | ~r2_hidden(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.76/2.11  tff(c_105, plain, (![A_39, A_18]: (r1_tarski(A_39, A_18) | ~r2_hidden(A_39, k1_zfmisc_1(A_18)))), inference(superposition, [status(thm), theory('equality')], [c_36, c_102])).
% 5.76/2.11  tff(c_358, plain, (![B_84, A_85]: (r1_tarski(B_84, A_85) | ~m1_subset_1(B_84, k1_zfmisc_1(A_85)) | v1_xboole_0(k1_zfmisc_1(A_85)))), inference(resolution, [status(thm)], [c_107, c_105])).
% 5.76/2.11  tff(c_369, plain, (r1_tarski('#skF_4', '#skF_2') | v1_xboole_0(k1_zfmisc_1('#skF_2'))), inference(resolution, [status(thm)], [c_48, c_358])).
% 5.76/2.11  tff(c_377, plain, (r1_tarski('#skF_4', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_96, c_369])).
% 5.76/2.11  tff(c_158, plain, (![A_48, B_49]: (~v1_xboole_0(A_48) | r1_tarski(A_48, B_49))), inference(resolution, [status(thm)], [c_140, c_30])).
% 5.76/2.11  tff(c_177, plain, (![B_54, A_55]: (B_54=A_55 | ~r1_tarski(B_54, A_55) | ~r1_tarski(A_55, B_54))), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.76/2.11  tff(c_184, plain, (![B_49, A_48]: (B_49=A_48 | ~r1_tarski(B_49, A_48) | ~v1_xboole_0(A_48))), inference(resolution, [status(thm)], [c_158, c_177])).
% 5.76/2.11  tff(c_386, plain, ('#skF_2'='#skF_4' | ~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_377, c_184])).
% 5.76/2.11  tff(c_415, plain, (~v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_386])).
% 5.76/2.11  tff(c_50, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_95])).
% 5.76/2.11  tff(c_372, plain, (r1_tarski('#skF_3', '#skF_2') | v1_xboole_0(k1_zfmisc_1('#skF_2'))), inference(resolution, [status(thm)], [c_50, c_358])).
% 5.76/2.11  tff(c_380, plain, (r1_tarski('#skF_3', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_96, c_372])).
% 5.76/2.11  tff(c_190, plain, (![C_56, B_57, A_58]: (r2_hidden(C_56, B_57) | ~r2_hidden(C_56, A_58) | ~r1_tarski(A_58, B_57))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.76/2.11  tff(c_1057, plain, (![B_125, B_126, A_127]: (r2_hidden(B_125, B_126) | ~r1_tarski(A_127, B_126) | ~m1_subset_1(B_125, A_127) | v1_xboole_0(A_127))), inference(resolution, [status(thm)], [c_40, c_190])).
% 5.76/2.11  tff(c_1061, plain, (![B_125]: (r2_hidden(B_125, '#skF_2') | ~m1_subset_1(B_125, '#skF_3') | v1_xboole_0('#skF_3'))), inference(resolution, [status(thm)], [c_380, c_1057])).
% 5.76/2.11  tff(c_1084, plain, (![B_128]: (r2_hidden(B_128, '#skF_2') | ~m1_subset_1(B_128, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_214, c_1061])).
% 5.76/2.11  tff(c_1093, plain, (![B_128]: (m1_subset_1(B_128, '#skF_2') | v1_xboole_0('#skF_2') | ~m1_subset_1(B_128, '#skF_3'))), inference(resolution, [status(thm)], [c_1084, c_38])).
% 5.76/2.11  tff(c_1122, plain, (![B_130]: (m1_subset_1(B_130, '#skF_2') | ~m1_subset_1(B_130, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_415, c_1093])).
% 5.76/2.11  tff(c_629, plain, (![B_107]: (r2_hidden('#skF_1'('#skF_3', B_107), '#skF_4') | ~m1_subset_1('#skF_1'('#skF_3', B_107), '#skF_2') | r1_tarski('#skF_3', B_107))), inference(resolution, [status(thm)], [c_140, c_54])).
% 5.76/2.11  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.76/2.11  tff(c_656, plain, (~m1_subset_1('#skF_1'('#skF_3', '#skF_4'), '#skF_2') | r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_629, c_4])).
% 5.76/2.11  tff(c_661, plain, (~m1_subset_1('#skF_1'('#skF_3', '#skF_4'), '#skF_2')), inference(splitLeft, [status(thm)], [c_656])).
% 5.76/2.11  tff(c_1139, plain, (~m1_subset_1('#skF_1'('#skF_3', '#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_1122, c_661])).
% 5.76/2.11  tff(c_1163, plain, (v1_xboole_0('#skF_3') | r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_155, c_1139])).
% 5.76/2.11  tff(c_1169, plain, (r1_tarski('#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_214, c_1163])).
% 5.76/2.11  tff(c_22, plain, (![B_10, A_9]: (B_10=A_9 | ~r1_tarski(B_10, A_9) | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.76/2.11  tff(c_1179, plain, ('#skF_3'='#skF_4' | ~r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_1169, c_22])).
% 5.76/2.11  tff(c_1188, plain, (~r1_tarski('#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_46, c_1179])).
% 5.76/2.11  tff(c_1063, plain, (![B_125]: (r2_hidden(B_125, '#skF_2') | ~m1_subset_1(B_125, '#skF_4') | v1_xboole_0('#skF_4'))), inference(resolution, [status(thm)], [c_377, c_1057])).
% 5.76/2.11  tff(c_1103, plain, (![B_129]: (r2_hidden(B_129, '#skF_2') | ~m1_subset_1(B_129, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_233, c_1063])).
% 5.76/2.11  tff(c_1112, plain, (![B_129]: (m1_subset_1(B_129, '#skF_2') | v1_xboole_0('#skF_2') | ~m1_subset_1(B_129, '#skF_4'))), inference(resolution, [status(thm)], [c_1103, c_38])).
% 5.76/2.11  tff(c_1197, plain, (![B_132]: (m1_subset_1(B_132, '#skF_2') | ~m1_subset_1(B_132, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_415, c_1112])).
% 5.76/2.11  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.76/2.11  tff(c_52, plain, (![D_25]: (r2_hidden(D_25, '#skF_3') | ~r2_hidden(D_25, '#skF_4') | ~m1_subset_1(D_25, '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_95])).
% 5.76/2.11  tff(c_160, plain, (![A_52, B_53]: (~r2_hidden('#skF_1'(A_52, B_53), B_53) | r1_tarski(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.76/2.11  tff(c_536, plain, (![A_99]: (r1_tarski(A_99, '#skF_3') | ~r2_hidden('#skF_1'(A_99, '#skF_3'), '#skF_4') | ~m1_subset_1('#skF_1'(A_99, '#skF_3'), '#skF_2'))), inference(resolution, [status(thm)], [c_52, c_160])).
% 5.76/2.11  tff(c_548, plain, (~m1_subset_1('#skF_1'('#skF_4', '#skF_3'), '#skF_2') | r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_6, c_536])).
% 5.76/2.11  tff(c_576, plain, (~m1_subset_1('#skF_1'('#skF_4', '#skF_3'), '#skF_2')), inference(splitLeft, [status(thm)], [c_548])).
% 5.76/2.11  tff(c_1219, plain, (~m1_subset_1('#skF_1'('#skF_4', '#skF_3'), '#skF_4')), inference(resolution, [status(thm)], [c_1197, c_576])).
% 5.76/2.11  tff(c_1246, plain, (v1_xboole_0('#skF_4') | r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_155, c_1219])).
% 5.76/2.11  tff(c_1253, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1188, c_233, c_1246])).
% 5.76/2.11  tff(c_1254, plain, (r1_tarski('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_656])).
% 5.76/2.11  tff(c_1260, plain, ('#skF_3'='#skF_4' | ~r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_1254, c_22])).
% 5.76/2.11  tff(c_1265, plain, (~r1_tarski('#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_46, c_1260])).
% 5.76/2.11  tff(c_1492, plain, (![B_144, B_145, A_146]: (r2_hidden(B_144, B_145) | ~r1_tarski(A_146, B_145) | ~m1_subset_1(B_144, A_146) | v1_xboole_0(A_146))), inference(resolution, [status(thm)], [c_40, c_190])).
% 5.76/2.11  tff(c_1500, plain, (![B_144]: (r2_hidden(B_144, '#skF_2') | ~m1_subset_1(B_144, '#skF_4') | v1_xboole_0('#skF_4'))), inference(resolution, [status(thm)], [c_377, c_1492])).
% 5.76/2.11  tff(c_1588, plain, (![B_150]: (r2_hidden(B_150, '#skF_2') | ~m1_subset_1(B_150, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_233, c_1500])).
% 5.76/2.11  tff(c_1597, plain, (![B_150]: (m1_subset_1(B_150, '#skF_2') | v1_xboole_0('#skF_2') | ~m1_subset_1(B_150, '#skF_4'))), inference(resolution, [status(thm)], [c_1588, c_38])).
% 5.76/2.11  tff(c_1786, plain, (![B_159]: (m1_subset_1(B_159, '#skF_2') | ~m1_subset_1(B_159, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_415, c_1597])).
% 5.76/2.11  tff(c_1804, plain, (~m1_subset_1('#skF_1'('#skF_4', '#skF_3'), '#skF_4')), inference(resolution, [status(thm)], [c_1786, c_576])).
% 5.76/2.11  tff(c_1812, plain, (v1_xboole_0('#skF_4') | r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_155, c_1804])).
% 5.76/2.11  tff(c_1819, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1265, c_233, c_1812])).
% 5.76/2.11  tff(c_1820, plain, (r1_tarski('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_548])).
% 5.76/2.11  tff(c_1826, plain, ('#skF_3'='#skF_4' | ~r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_1820, c_22])).
% 5.76/2.11  tff(c_1831, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_46, c_1826])).
% 5.76/2.11  tff(c_2117, plain, (![B_174, B_175, A_176]: (r2_hidden(B_174, B_175) | ~r1_tarski(A_176, B_175) | ~m1_subset_1(B_174, A_176) | v1_xboole_0(A_176))), inference(resolution, [status(thm)], [c_40, c_190])).
% 5.76/2.11  tff(c_2123, plain, (![B_174]: (r2_hidden(B_174, '#skF_2') | ~m1_subset_1(B_174, '#skF_3') | v1_xboole_0('#skF_3'))), inference(resolution, [status(thm)], [c_380, c_2117])).
% 5.76/2.11  tff(c_2334, plain, (![B_184]: (r2_hidden(B_184, '#skF_2') | ~m1_subset_1(B_184, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_214, c_2123])).
% 5.76/2.11  tff(c_2343, plain, (![B_184]: (m1_subset_1(B_184, '#skF_2') | v1_xboole_0('#skF_2') | ~m1_subset_1(B_184, '#skF_3'))), inference(resolution, [status(thm)], [c_2334, c_38])).
% 5.76/2.11  tff(c_2403, plain, (![B_187]: (m1_subset_1(B_187, '#skF_2') | ~m1_subset_1(B_187, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_415, c_2343])).
% 5.76/2.11  tff(c_1879, plain, (![B_165]: (r2_hidden('#skF_1'('#skF_3', B_165), '#skF_4') | ~m1_subset_1('#skF_1'('#skF_3', B_165), '#skF_2') | r1_tarski('#skF_3', B_165))), inference(resolution, [status(thm)], [c_140, c_54])).
% 5.76/2.11  tff(c_1894, plain, (~m1_subset_1('#skF_1'('#skF_3', '#skF_4'), '#skF_2') | r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_1879, c_4])).
% 5.76/2.11  tff(c_1908, plain, (~m1_subset_1('#skF_1'('#skF_3', '#skF_4'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_1831, c_1831, c_1894])).
% 5.76/2.11  tff(c_2418, plain, (~m1_subset_1('#skF_1'('#skF_3', '#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_2403, c_1908])).
% 5.76/2.11  tff(c_2428, plain, (v1_xboole_0('#skF_3') | r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_155, c_2418])).
% 5.76/2.11  tff(c_2436, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1831, c_214, c_2428])).
% 5.76/2.11  tff(c_2437, plain, ('#skF_2'='#skF_4'), inference(splitRight, [status(thm)], [c_386])).
% 5.76/2.11  tff(c_2438, plain, (v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_386])).
% 5.76/2.11  tff(c_2454, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2437, c_2438])).
% 5.76/2.11  tff(c_2455, plain, $false, inference(negUnitSimplification, [status(thm)], [c_233, c_2454])).
% 5.76/2.11  tff(c_2522, plain, (![B_194]: (~m1_subset_1(B_194, '#skF_2') | ~m1_subset_1(B_194, '#skF_3'))), inference(splitRight, [status(thm)], [c_232])).
% 5.76/2.11  tff(c_2527, plain, (![B_20]: (~m1_subset_1(B_20, '#skF_3') | ~v1_xboole_0(B_20) | ~v1_xboole_0('#skF_2'))), inference(resolution, [status(thm)], [c_42, c_2522])).
% 5.76/2.11  tff(c_2528, plain, (~v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_2527])).
% 5.76/2.11  tff(c_3280, plain, (![B_267, A_268]: (r1_tarski(B_267, A_268) | ~m1_subset_1(B_267, k1_zfmisc_1(A_268)) | v1_xboole_0(k1_zfmisc_1(A_268)))), inference(resolution, [status(thm)], [c_107, c_105])).
% 5.76/2.11  tff(c_3297, plain, (r1_tarski('#skF_3', '#skF_2') | v1_xboole_0(k1_zfmisc_1('#skF_2'))), inference(resolution, [status(thm)], [c_50, c_3280])).
% 5.76/2.11  tff(c_3306, plain, (r1_tarski('#skF_3', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_96, c_3297])).
% 5.76/2.11  tff(c_199, plain, (![B_20, B_57, A_19]: (r2_hidden(B_20, B_57) | ~r1_tarski(A_19, B_57) | ~m1_subset_1(B_20, A_19) | v1_xboole_0(A_19))), inference(resolution, [status(thm)], [c_40, c_190])).
% 5.76/2.11  tff(c_3310, plain, (![B_20]: (r2_hidden(B_20, '#skF_2') | ~m1_subset_1(B_20, '#skF_3') | v1_xboole_0('#skF_3'))), inference(resolution, [status(thm)], [c_3306, c_199])).
% 5.76/2.11  tff(c_3342, plain, (![B_273]: (r2_hidden(B_273, '#skF_2') | ~m1_subset_1(B_273, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_214, c_3310])).
% 5.76/2.11  tff(c_3351, plain, (![B_273]: (m1_subset_1(B_273, '#skF_2') | v1_xboole_0('#skF_2') | ~m1_subset_1(B_273, '#skF_3'))), inference(resolution, [status(thm)], [c_3342, c_38])).
% 5.76/2.11  tff(c_3361, plain, (![B_274]: (m1_subset_1(B_274, '#skF_2') | ~m1_subset_1(B_274, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_2528, c_3351])).
% 5.76/2.11  tff(c_2456, plain, (![B_61]: (~m1_subset_1(B_61, '#skF_2') | ~m1_subset_1(B_61, '#skF_3'))), inference(splitRight, [status(thm)], [c_232])).
% 5.76/2.11  tff(c_3410, plain, (![B_276]: (~m1_subset_1(B_276, '#skF_3'))), inference(resolution, [status(thm)], [c_3361, c_2456])).
% 5.76/2.11  tff(c_3414, plain, (![B_49]: (v1_xboole_0('#skF_3') | r1_tarski('#skF_3', B_49))), inference(resolution, [status(thm)], [c_155, c_3410])).
% 5.76/2.11  tff(c_3427, plain, (![B_277]: (r1_tarski('#skF_3', B_277))), inference(negUnitSimplification, [status(thm)], [c_214, c_3414])).
% 5.76/2.11  tff(c_2457, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_232])).
% 5.76/2.11  tff(c_8, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.76/2.11  tff(c_76, plain, (![B_31, A_32]: (~v1_xboole_0(B_31) | B_31=A_32 | ~v1_xboole_0(A_32))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.76/2.11  tff(c_79, plain, (![A_32]: (k1_xboole_0=A_32 | ~v1_xboole_0(A_32))), inference(resolution, [status(thm)], [c_8, c_76])).
% 5.76/2.11  tff(c_2463, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_2457, c_79])).
% 5.76/2.11  tff(c_28, plain, (![A_11]: (k5_xboole_0(A_11, k1_xboole_0)=A_11)), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.76/2.11  tff(c_2480, plain, (![A_11]: (k5_xboole_0(A_11, '#skF_4')=A_11)), inference(demodulation, [status(thm), theory('equality')], [c_2463, c_28])).
% 5.76/2.11  tff(c_2533, plain, (![A_197, B_198, C_199]: (r2_hidden(A_197, B_198) | ~r2_hidden(A_197, C_199) | r2_hidden(A_197, k5_xboole_0(B_198, C_199)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.76/2.11  tff(c_2568, plain, (![A_202, A_203]: (r2_hidden(A_202, A_203) | ~r2_hidden(A_202, '#skF_4') | r2_hidden(A_202, A_203))), inference(superposition, [status(thm), theory('equality')], [c_2480, c_2533])).
% 5.76/2.11  tff(c_2578, plain, (![B_204, A_205]: (r2_hidden('#skF_1'('#skF_4', B_204), A_205) | r1_tarski('#skF_4', B_204))), inference(resolution, [status(thm)], [c_6, c_2568])).
% 5.76/2.11  tff(c_2639, plain, (![A_208]: (r1_tarski('#skF_4', A_208))), inference(resolution, [status(thm)], [c_2578, c_4])).
% 5.76/2.11  tff(c_2646, plain, (![A_208]: (A_208='#skF_4' | ~r1_tarski(A_208, '#skF_4'))), inference(resolution, [status(thm)], [c_2639, c_22])).
% 5.76/2.11  tff(c_3435, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_3427, c_2646])).
% 5.76/2.11  tff(c_3448, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_3435])).
% 5.76/2.11  tff(c_3450, plain, (v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_2527])).
% 5.76/2.11  tff(c_32, plain, (![B_15, A_14]: (~v1_xboole_0(B_15) | B_15=A_14 | ~v1_xboole_0(A_14))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.76/2.11  tff(c_2464, plain, (![A_14]: (A_14='#skF_4' | ~v1_xboole_0(A_14))), inference(resolution, [status(thm)], [c_2457, c_32])).
% 5.76/2.11  tff(c_3456, plain, ('#skF_2'='#skF_4'), inference(resolution, [status(thm)], [c_3450, c_2464])).
% 5.76/2.11  tff(c_3462, plain, (~v1_xboole_0(k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_3456, c_96])).
% 5.76/2.11  tff(c_3465, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_3456, c_50])).
% 5.76/2.11  tff(c_4238, plain, (![B_347, A_348]: (r1_tarski(B_347, A_348) | ~m1_subset_1(B_347, k1_zfmisc_1(A_348)) | v1_xboole_0(k1_zfmisc_1(A_348)))), inference(resolution, [status(thm)], [c_107, c_105])).
% 5.76/2.11  tff(c_4248, plain, (r1_tarski('#skF_3', '#skF_4') | v1_xboole_0(k1_zfmisc_1('#skF_4'))), inference(resolution, [status(thm)], [c_3465, c_4238])).
% 5.76/2.11  tff(c_4259, plain, (r1_tarski('#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_3462, c_4248])).
% 5.76/2.11  tff(c_3568, plain, (![A_289, B_290, C_291]: (r2_hidden(A_289, B_290) | ~r2_hidden(A_289, C_291) | r2_hidden(A_289, k5_xboole_0(B_290, C_291)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.76/2.11  tff(c_3604, plain, (![A_293, A_294]: (r2_hidden(A_293, A_294) | ~r2_hidden(A_293, '#skF_4') | r2_hidden(A_293, A_294))), inference(superposition, [status(thm), theory('equality')], [c_2480, c_3568])).
% 5.76/2.11  tff(c_3614, plain, (![B_295, A_296]: (r2_hidden('#skF_1'('#skF_4', B_295), A_296) | r1_tarski('#skF_4', B_295))), inference(resolution, [status(thm)], [c_6, c_3604])).
% 5.76/2.11  tff(c_3676, plain, (![A_299]: (r1_tarski('#skF_4', A_299))), inference(resolution, [status(thm)], [c_3614, c_4])).
% 5.76/2.11  tff(c_3683, plain, (![A_299]: (A_299='#skF_4' | ~r1_tarski(A_299, '#skF_4'))), inference(resolution, [status(thm)], [c_3676, c_22])).
% 5.76/2.11  tff(c_4282, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_4259, c_3683])).
% 5.76/2.11  tff(c_4297, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_4282])).
% 5.76/2.11  tff(c_4331, plain, (![D_355]: (~r2_hidden(D_355, '#skF_4') | ~m1_subset_1(D_355, '#skF_2'))), inference(splitRight, [status(thm)], [c_130])).
% 5.76/2.11  tff(c_4341, plain, (![B_20]: (~m1_subset_1(B_20, '#skF_2') | ~m1_subset_1(B_20, '#skF_4') | v1_xboole_0('#skF_4'))), inference(resolution, [status(thm)], [c_40, c_4331])).
% 5.76/2.11  tff(c_4362, plain, (![B_360]: (~m1_subset_1(B_360, '#skF_2') | ~m1_subset_1(B_360, '#skF_4'))), inference(splitLeft, [status(thm)], [c_4341])).
% 5.76/2.11  tff(c_4367, plain, (![B_20]: (~m1_subset_1(B_20, '#skF_4') | ~v1_xboole_0(B_20) | ~v1_xboole_0('#skF_2'))), inference(resolution, [status(thm)], [c_42, c_4362])).
% 5.76/2.11  tff(c_4368, plain, (~v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_4367])).
% 5.76/2.11  tff(c_4441, plain, (![A_372, B_373]: (m1_subset_1('#skF_1'(A_372, B_373), A_372) | v1_xboole_0(A_372) | r1_tarski(A_372, B_373))), inference(resolution, [status(thm)], [c_140, c_38])).
% 5.76/2.11  tff(c_4361, plain, (![B_20]: (~m1_subset_1(B_20, '#skF_2') | ~m1_subset_1(B_20, '#skF_4'))), inference(splitLeft, [status(thm)], [c_4341])).
% 5.76/2.11  tff(c_4445, plain, (![B_373]: (~m1_subset_1('#skF_1'('#skF_2', B_373), '#skF_4') | v1_xboole_0('#skF_2') | r1_tarski('#skF_2', B_373))), inference(resolution, [status(thm)], [c_4441, c_4361])).
% 5.76/2.11  tff(c_4453, plain, (![B_374]: (~m1_subset_1('#skF_1'('#skF_2', B_374), '#skF_4') | r1_tarski('#skF_2', B_374))), inference(negUnitSimplification, [status(thm)], [c_4368, c_4445])).
% 5.76/2.11  tff(c_4457, plain, (![B_374]: (r1_tarski('#skF_2', B_374) | ~v1_xboole_0('#skF_1'('#skF_2', B_374)) | ~v1_xboole_0('#skF_4'))), inference(resolution, [status(thm)], [c_42, c_4453])).
% 5.76/2.11  tff(c_4458, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_4457])).
% 5.76/2.11  tff(c_4819, plain, (![B_407, A_408]: (r1_tarski(B_407, A_408) | ~m1_subset_1(B_407, k1_zfmisc_1(A_408)) | v1_xboole_0(k1_zfmisc_1(A_408)))), inference(resolution, [status(thm)], [c_107, c_105])).
% 5.76/2.11  tff(c_4833, plain, (r1_tarski('#skF_4', '#skF_2') | v1_xboole_0(k1_zfmisc_1('#skF_2'))), inference(resolution, [status(thm)], [c_48, c_4819])).
% 5.76/2.11  tff(c_4842, plain, (r1_tarski('#skF_4', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_96, c_4833])).
% 5.76/2.11  tff(c_4847, plain, (![B_20]: (r2_hidden(B_20, '#skF_2') | ~m1_subset_1(B_20, '#skF_4') | v1_xboole_0('#skF_4'))), inference(resolution, [status(thm)], [c_4842, c_199])).
% 5.76/2.11  tff(c_4863, plain, (![B_409]: (r2_hidden(B_409, '#skF_2') | ~m1_subset_1(B_409, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_4458, c_4847])).
% 5.76/2.11  tff(c_4872, plain, (![B_409]: (m1_subset_1(B_409, '#skF_2') | v1_xboole_0('#skF_2') | ~m1_subset_1(B_409, '#skF_4'))), inference(resolution, [status(thm)], [c_4863, c_38])).
% 5.76/2.11  tff(c_4882, plain, (![B_410]: (m1_subset_1(B_410, '#skF_2') | ~m1_subset_1(B_410, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_4368, c_4872])).
% 5.76/2.11  tff(c_4981, plain, (![B_414]: (~m1_subset_1(B_414, '#skF_4'))), inference(resolution, [status(thm)], [c_4882, c_4361])).
% 5.76/2.11  tff(c_4985, plain, (![B_49]: (v1_xboole_0('#skF_4') | r1_tarski('#skF_4', B_49))), inference(resolution, [status(thm)], [c_155, c_4981])).
% 5.76/2.11  tff(c_4996, plain, (![B_415]: (r1_tarski('#skF_4', B_415))), inference(negUnitSimplification, [status(thm)], [c_4458, c_4985])).
% 5.76/2.11  tff(c_4299, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_130])).
% 5.76/2.11  tff(c_4305, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_4299, c_79])).
% 5.76/2.11  tff(c_4308, plain, (![A_11]: (k5_xboole_0(A_11, '#skF_3')=A_11)), inference(demodulation, [status(thm), theory('equality')], [c_4305, c_28])).
% 5.76/2.11  tff(c_4482, plain, (![A_382, B_383, C_384]: (r2_hidden(A_382, B_383) | ~r2_hidden(A_382, C_384) | r2_hidden(A_382, k5_xboole_0(B_383, C_384)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.76/2.11  tff(c_4506, plain, (![A_385, A_386]: (r2_hidden(A_385, A_386) | ~r2_hidden(A_385, '#skF_3') | r2_hidden(A_385, A_386))), inference(superposition, [status(thm), theory('equality')], [c_4308, c_4482])).
% 5.76/2.11  tff(c_4516, plain, (![B_387, A_388]: (r2_hidden('#skF_1'('#skF_3', B_387), A_388) | r1_tarski('#skF_3', B_387))), inference(resolution, [status(thm)], [c_6, c_4506])).
% 5.76/2.11  tff(c_4568, plain, (![A_389]: (r1_tarski('#skF_3', A_389))), inference(resolution, [status(thm)], [c_4516, c_4])).
% 5.76/2.11  tff(c_4575, plain, (![A_389]: (A_389='#skF_3' | ~r1_tarski(A_389, '#skF_3'))), inference(resolution, [status(thm)], [c_4568, c_22])).
% 5.76/2.11  tff(c_5002, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_4996, c_4575])).
% 5.76/2.11  tff(c_5013, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_5002])).
% 5.76/2.11  tff(c_5015, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_4457])).
% 5.76/2.11  tff(c_4306, plain, (![A_14]: (A_14='#skF_3' | ~v1_xboole_0(A_14))), inference(resolution, [status(thm)], [c_4299, c_32])).
% 5.76/2.11  tff(c_5018, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_5015, c_4306])).
% 5.76/2.11  tff(c_5024, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_5018])).
% 5.76/2.11  tff(c_5026, plain, (v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_4367])).
% 5.76/2.11  tff(c_5033, plain, ('#skF_2'='#skF_3'), inference(resolution, [status(thm)], [c_5026, c_4306])).
% 5.76/2.11  tff(c_5039, plain, (~v1_xboole_0(k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_5033, c_96])).
% 5.76/2.11  tff(c_5041, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_5033, c_48])).
% 5.76/2.11  tff(c_5743, plain, (![B_482, A_483]: (r1_tarski(B_482, A_483) | ~m1_subset_1(B_482, k1_zfmisc_1(A_483)) | v1_xboole_0(k1_zfmisc_1(A_483)))), inference(resolution, [status(thm)], [c_107, c_105])).
% 5.76/2.11  tff(c_5753, plain, (r1_tarski('#skF_4', '#skF_3') | v1_xboole_0(k1_zfmisc_1('#skF_3'))), inference(resolution, [status(thm)], [c_5041, c_5743])).
% 5.76/2.11  tff(c_5764, plain, (r1_tarski('#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_5039, c_5753])).
% 5.76/2.11  tff(c_5053, plain, (![A_416, B_417, C_418]: (r2_hidden(A_416, B_417) | ~r2_hidden(A_416, C_418) | r2_hidden(A_416, k5_xboole_0(B_417, C_418)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.76/2.11  tff(c_5170, plain, (![A_432, A_433]: (r2_hidden(A_432, A_433) | ~r2_hidden(A_432, '#skF_3') | r2_hidden(A_432, A_433))), inference(superposition, [status(thm), theory('equality')], [c_4308, c_5053])).
% 5.76/2.11  tff(c_5180, plain, (![B_434, A_435]: (r2_hidden('#skF_1'('#skF_3', B_434), A_435) | r1_tarski('#skF_3', B_434))), inference(resolution, [status(thm)], [c_6, c_5170])).
% 5.76/2.11  tff(c_5227, plain, (![A_436]: (r1_tarski('#skF_3', A_436))), inference(resolution, [status(thm)], [c_5180, c_4])).
% 5.76/2.11  tff(c_5234, plain, (![A_436]: (A_436='#skF_3' | ~r1_tarski(A_436, '#skF_3'))), inference(resolution, [status(thm)], [c_5227, c_22])).
% 5.76/2.11  tff(c_5772, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_5764, c_5234])).
% 5.76/2.11  tff(c_5787, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_5772])).
% 5.76/2.11  tff(c_5788, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_4341])).
% 5.76/2.11  tff(c_5791, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_5788, c_4306])).
% 5.76/2.11  tff(c_5797, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_5791])).
% 5.76/2.11  tff(c_5798, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_94])).
% 5.76/2.11  tff(c_5799, plain, (v1_xboole_0(k1_zfmisc_1('#skF_2'))), inference(splitRight, [status(thm)], [c_94])).
% 5.76/2.11  tff(c_5832, plain, (![A_487]: (A_487='#skF_4' | ~v1_xboole_0(A_487))), inference(resolution, [status(thm)], [c_5798, c_32])).
% 5.76/2.11  tff(c_5839, plain, (k1_zfmisc_1('#skF_2')='#skF_4'), inference(resolution, [status(thm)], [c_5799, c_5832])).
% 5.76/2.11  tff(c_5844, plain, (m1_subset_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5839, c_50])).
% 5.76/2.11  tff(c_44, plain, (![B_20, A_19]: (v1_xboole_0(B_20) | ~m1_subset_1(B_20, A_19) | ~v1_xboole_0(A_19))), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.76/2.11  tff(c_5861, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_5844, c_44])).
% 5.76/2.11  tff(c_5864, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5798, c_5861])).
% 5.76/2.11  tff(c_5811, plain, (![A_14]: (A_14='#skF_4' | ~v1_xboole_0(A_14))), inference(resolution, [status(thm)], [c_5798, c_32])).
% 5.76/2.11  tff(c_5867, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_5864, c_5811])).
% 5.76/2.11  tff(c_5873, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_5867])).
% 5.76/2.11  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.76/2.11  
% 5.76/2.11  Inference rules
% 5.76/2.11  ----------------------
% 5.76/2.11  #Ref     : 0
% 5.76/2.11  #Sup     : 1253
% 5.76/2.11  #Fact    : 0
% 5.76/2.11  #Define  : 0
% 5.76/2.11  #Split   : 39
% 5.76/2.11  #Chain   : 0
% 5.76/2.11  #Close   : 0
% 5.76/2.11  
% 5.76/2.11  Ordering : KBO
% 5.76/2.11  
% 5.76/2.11  Simplification rules
% 5.76/2.11  ----------------------
% 5.76/2.11  #Subsume      : 246
% 5.76/2.11  #Demod        : 438
% 5.76/2.11  #Tautology    : 396
% 5.76/2.11  #SimpNegUnit  : 113
% 5.76/2.11  #BackRed      : 67
% 5.76/2.11  
% 5.76/2.11  #Partial instantiations: 0
% 5.76/2.11  #Strategies tried      : 1
% 5.76/2.11  
% 5.76/2.11  Timing (in seconds)
% 5.76/2.11  ----------------------
% 5.76/2.11  Preprocessing        : 0.30
% 5.76/2.11  Parsing              : 0.16
% 5.76/2.11  CNF conversion       : 0.02
% 5.76/2.11  Main loop            : 1.00
% 5.76/2.11  Inferencing          : 0.36
% 5.76/2.11  Reduction            : 0.29
% 5.76/2.11  Demodulation         : 0.19
% 5.76/2.11  BG Simplification    : 0.04
% 5.76/2.11  Subsumption          : 0.23
% 5.76/2.11  Abstraction          : 0.04
% 5.76/2.11  MUC search           : 0.00
% 5.76/2.11  Cooper               : 0.00
% 5.76/2.11  Total                : 1.37
% 5.76/2.11  Index Insertion      : 0.00
% 5.76/2.11  Index Deletion       : 0.00
% 5.76/2.11  Index Matching       : 0.00
% 5.76/2.11  BG Taut test         : 0.00
%------------------------------------------------------------------------------
