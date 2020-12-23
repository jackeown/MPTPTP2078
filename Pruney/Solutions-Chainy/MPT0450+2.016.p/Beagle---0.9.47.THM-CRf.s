%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:38 EST 2020

% Result     : Theorem 11.94s
% Output     : CNFRefutation 11.94s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 199 expanded)
%              Number of leaves         :   25 (  79 expanded)
%              Depth                    :   12
%              Number of atoms          :  155 ( 504 expanded)
%              Number of equality atoms :   31 ( 104 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k3_relat_1 > k1_zfmisc_1 > k1_setfam_1 > #skF_1 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_36,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_76,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => r1_tarski(k3_relat_1(k3_xboole_0(A,B)),k3_xboole_0(k3_relat_1(A),k3_relat_1(B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_relat_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_59,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_68,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => r1_tarski(k3_relat_1(A),k3_relat_1(B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_relat_1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

tff(c_16,plain,(
    ! [A_1,B_2,C_3] :
      ( r2_hidden('#skF_1'(A_1,B_2,C_3),B_2)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),C_3)
      | k3_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_186,plain,(
    ! [A_71,B_72,C_73] :
      ( ~ r2_hidden('#skF_1'(A_71,B_72,C_73),C_73)
      | r2_hidden('#skF_2'(A_71,B_72,C_73),C_73)
      | k3_xboole_0(A_71,B_72) = C_73 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_195,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_2'(A_1,B_2,B_2),B_2)
      | k3_xboole_0(A_1,B_2) = B_2 ) ),
    inference(resolution,[status(thm)],[c_16,c_186])).

tff(c_145,plain,(
    ! [A_66,B_67,C_68] :
      ( r2_hidden('#skF_1'(A_66,B_67,C_68),B_67)
      | r2_hidden('#skF_2'(A_66,B_67,C_68),C_68)
      | k3_xboole_0(A_66,B_67) = C_68 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k3_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_492,plain,(
    ! [A_109,B_110,A_111,B_112] :
      ( r2_hidden('#skF_2'(A_109,B_110,k3_xboole_0(A_111,B_112)),B_112)
      | r2_hidden('#skF_1'(A_109,B_110,k3_xboole_0(A_111,B_112)),B_110)
      | k3_xboole_0(A_111,B_112) = k3_xboole_0(A_109,B_110) ) ),
    inference(resolution,[status(thm)],[c_145,c_4])).

tff(c_10,plain,(
    ! [A_1,B_2,C_3] :
      ( r2_hidden('#skF_1'(A_1,B_2,C_3),B_2)
      | ~ r2_hidden('#skF_2'(A_1,B_2,C_3),B_2)
      | ~ r2_hidden('#skF_2'(A_1,B_2,C_3),A_1)
      | k3_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_526,plain,(
    ! [B_112,B_110,A_111] :
      ( ~ r2_hidden('#skF_2'(B_112,B_110,k3_xboole_0(A_111,B_112)),B_110)
      | r2_hidden('#skF_1'(B_112,B_110,k3_xboole_0(A_111,B_112)),B_110)
      | k3_xboole_0(B_112,B_110) = k3_xboole_0(A_111,B_112) ) ),
    inference(resolution,[status(thm)],[c_492,c_10])).

tff(c_208,plain,(
    ! [A_76,B_77,C_78] :
      ( r2_hidden('#skF_1'(A_76,B_77,C_78),A_76)
      | r2_hidden('#skF_2'(A_76,B_77,C_78),C_78)
      | k3_xboole_0(A_76,B_77) = C_78 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_14,plain,(
    ! [A_1,B_2,C_3] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2,C_3),C_3)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),C_3)
      | k3_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_229,plain,(
    ! [A_76,B_77] :
      ( r2_hidden('#skF_2'(A_76,B_77,A_76),A_76)
      | k3_xboole_0(A_76,B_77) = A_76 ) ),
    inference(resolution,[status(thm)],[c_208,c_14])).

tff(c_18,plain,(
    ! [A_1,B_2,C_3] :
      ( r2_hidden('#skF_1'(A_1,B_2,C_3),A_1)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),C_3)
      | k3_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_330,plain,(
    ! [A_98,B_99,C_100] :
      ( r2_hidden('#skF_1'(A_98,B_99,C_100),A_98)
      | ~ r2_hidden('#skF_2'(A_98,B_99,C_100),B_99)
      | ~ r2_hidden('#skF_2'(A_98,B_99,C_100),A_98)
      | k3_xboole_0(A_98,B_99) = C_100 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_352,plain,(
    ! [A_1,C_3] :
      ( ~ r2_hidden('#skF_2'(A_1,C_3,C_3),A_1)
      | r2_hidden('#skF_1'(A_1,C_3,C_3),A_1)
      | k3_xboole_0(A_1,C_3) = C_3 ) ),
    inference(resolution,[status(thm)],[c_18,c_330])).

tff(c_371,plain,(
    ! [A_103,B_104,C_105] :
      ( ~ r2_hidden('#skF_1'(A_103,B_104,C_105),C_105)
      | ~ r2_hidden('#skF_2'(A_103,B_104,C_105),B_104)
      | ~ r2_hidden('#skF_2'(A_103,B_104,C_105),A_103)
      | k3_xboole_0(A_103,B_104) = C_105 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_392,plain,(
    ! [A_106] :
      ( ~ r2_hidden('#skF_2'(A_106,A_106,A_106),A_106)
      | k3_xboole_0(A_106,A_106) = A_106 ) ),
    inference(resolution,[status(thm)],[c_352,c_371])).

tff(c_409,plain,(
    ! [B_77] : k3_xboole_0(B_77,B_77) = B_77 ),
    inference(resolution,[status(thm)],[c_229,c_392])).

tff(c_6,plain,(
    ! [D_6,A_1,B_2] :
      ( r2_hidden(D_6,A_1)
      | ~ r2_hidden(D_6,k3_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_535,plain,(
    ! [A_113,B_114,A_115,B_116] :
      ( r2_hidden('#skF_2'(A_113,B_114,k3_xboole_0(A_115,B_116)),A_115)
      | r2_hidden('#skF_1'(A_113,B_114,k3_xboole_0(A_115,B_116)),B_114)
      | k3_xboole_0(A_115,B_116) = k3_xboole_0(A_113,B_114) ) ),
    inference(resolution,[status(thm)],[c_145,c_6])).

tff(c_574,plain,(
    ! [A_113,B_2,A_1,A_115,B_116] :
      ( r2_hidden('#skF_1'(A_113,k3_xboole_0(A_1,B_2),k3_xboole_0(A_115,B_116)),B_2)
      | r2_hidden('#skF_2'(A_113,k3_xboole_0(A_1,B_2),k3_xboole_0(A_115,B_116)),A_115)
      | k3_xboole_0(A_115,B_116) = k3_xboole_0(A_113,k3_xboole_0(A_1,B_2)) ) ),
    inference(resolution,[status(thm)],[c_535,c_4])).

tff(c_575,plain,(
    ! [A_113,B_2,A_1,A_115,B_116] :
      ( r2_hidden('#skF_1'(A_113,k3_xboole_0(A_1,B_2),k3_xboole_0(A_115,B_116)),A_1)
      | r2_hidden('#skF_2'(A_113,k3_xboole_0(A_1,B_2),k3_xboole_0(A_115,B_116)),A_115)
      | k3_xboole_0(A_115,B_116) = k3_xboole_0(A_113,k3_xboole_0(A_1,B_2)) ) ),
    inference(resolution,[status(thm)],[c_535,c_6])).

tff(c_2,plain,(
    ! [D_6,A_1,B_2] :
      ( r2_hidden(D_6,k3_xboole_0(A_1,B_2))
      | ~ r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_905,plain,(
    ! [A_150,B_151,A_152,B_153] :
      ( r2_hidden('#skF_2'(A_150,B_151,k3_xboole_0(A_152,B_153)),k3_xboole_0(A_152,B_153))
      | k3_xboole_0(A_152,B_153) = k3_xboole_0(A_150,B_151)
      | ~ r2_hidden('#skF_1'(A_150,B_151,k3_xboole_0(A_152,B_153)),B_153)
      | ~ r2_hidden('#skF_1'(A_150,B_151,k3_xboole_0(A_152,B_153)),A_152) ) ),
    inference(resolution,[status(thm)],[c_2,c_186])).

tff(c_6505,plain,(
    ! [A_566,B_567,A_568,B_569] :
      ( r2_hidden('#skF_2'(A_566,B_567,k3_xboole_0(A_568,B_569)),A_568)
      | k3_xboole_0(A_568,B_569) = k3_xboole_0(A_566,B_567)
      | ~ r2_hidden('#skF_1'(A_566,B_567,k3_xboole_0(A_568,B_569)),B_569)
      | ~ r2_hidden('#skF_1'(A_566,B_567,k3_xboole_0(A_568,B_569)),A_568) ) ),
    inference(resolution,[status(thm)],[c_905,c_6])).

tff(c_9578,plain,(
    ! [A_707,A_708,B_709,A_710] :
      ( ~ r2_hidden('#skF_1'(A_707,k3_xboole_0(A_708,B_709),k3_xboole_0(A_710,A_708)),A_710)
      | r2_hidden('#skF_2'(A_707,k3_xboole_0(A_708,B_709),k3_xboole_0(A_710,A_708)),A_710)
      | k3_xboole_0(A_710,A_708) = k3_xboole_0(A_707,k3_xboole_0(A_708,B_709)) ) ),
    inference(resolution,[status(thm)],[c_575,c_6505])).

tff(c_9992,plain,(
    ! [A_715,B_716,B_717] :
      ( r2_hidden('#skF_2'(A_715,k3_xboole_0(B_716,B_717),k3_xboole_0(B_717,B_716)),B_717)
      | k3_xboole_0(A_715,k3_xboole_0(B_716,B_717)) = k3_xboole_0(B_717,B_716) ) ),
    inference(resolution,[status(thm)],[c_574,c_9578])).

tff(c_10039,plain,(
    ! [A_715,B_716,A_1,B_2] :
      ( r2_hidden('#skF_2'(A_715,k3_xboole_0(B_716,k3_xboole_0(A_1,B_2)),k3_xboole_0(k3_xboole_0(A_1,B_2),B_716)),B_2)
      | k3_xboole_0(A_715,k3_xboole_0(B_716,k3_xboole_0(A_1,B_2))) = k3_xboole_0(k3_xboole_0(A_1,B_2),B_716) ) ),
    inference(resolution,[status(thm)],[c_9992,c_4])).

tff(c_2343,plain,(
    ! [A_263,B_264,A_265,B_266] :
      ( ~ r2_hidden('#skF_2'(A_263,B_264,k3_xboole_0(A_265,B_266)),B_264)
      | ~ r2_hidden('#skF_2'(A_263,B_264,k3_xboole_0(A_265,B_266)),A_263)
      | k3_xboole_0(A_265,B_266) = k3_xboole_0(A_263,B_264)
      | ~ r2_hidden('#skF_1'(A_263,B_264,k3_xboole_0(A_265,B_266)),B_266)
      | ~ r2_hidden('#skF_1'(A_263,B_264,k3_xboole_0(A_265,B_266)),A_265) ) ),
    inference(resolution,[status(thm)],[c_2,c_371])).

tff(c_11139,plain,(
    ! [A_768,A_769,B_770] :
      ( ~ r2_hidden('#skF_2'(A_768,k3_xboole_0(A_769,B_770),k3_xboole_0(A_769,B_770)),A_768)
      | ~ r2_hidden('#skF_1'(A_768,k3_xboole_0(A_769,B_770),k3_xboole_0(A_769,B_770)),B_770)
      | ~ r2_hidden('#skF_1'(A_768,k3_xboole_0(A_769,B_770),k3_xboole_0(A_769,B_770)),A_769)
      | k3_xboole_0(A_768,k3_xboole_0(A_769,B_770)) = k3_xboole_0(A_769,B_770) ) ),
    inference(resolution,[status(thm)],[c_195,c_2343])).

tff(c_11145,plain,(
    ! [B_2,A_1] :
      ( ~ r2_hidden('#skF_1'(B_2,k3_xboole_0(k3_xboole_0(A_1,B_2),k3_xboole_0(A_1,B_2)),k3_xboole_0(k3_xboole_0(A_1,B_2),k3_xboole_0(A_1,B_2))),k3_xboole_0(A_1,B_2))
      | k3_xboole_0(B_2,k3_xboole_0(k3_xboole_0(A_1,B_2),k3_xboole_0(A_1,B_2))) = k3_xboole_0(k3_xboole_0(A_1,B_2),k3_xboole_0(A_1,B_2)) ) ),
    inference(resolution,[status(thm)],[c_10039,c_11139])).

tff(c_11418,plain,(
    ! [B_773,A_774] :
      ( ~ r2_hidden('#skF_1'(B_773,k3_xboole_0(A_774,B_773),k3_xboole_0(A_774,B_773)),k3_xboole_0(A_774,B_773))
      | k3_xboole_0(B_773,k3_xboole_0(A_774,B_773)) = k3_xboole_0(A_774,B_773) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_409,c_409,c_409,c_409,c_11145])).

tff(c_13747,plain,(
    ! [B_781,A_782] :
      ( ~ r2_hidden('#skF_2'(B_781,k3_xboole_0(A_782,B_781),k3_xboole_0(A_782,B_781)),k3_xboole_0(A_782,B_781))
      | k3_xboole_0(B_781,k3_xboole_0(A_782,B_781)) = k3_xboole_0(A_782,B_781) ) ),
    inference(resolution,[status(thm)],[c_526,c_11418])).

tff(c_13858,plain,(
    ! [A_783,A_784] : k3_xboole_0(A_783,k3_xboole_0(A_784,A_783)) = k3_xboole_0(A_784,A_783) ),
    inference(resolution,[status(thm)],[c_195,c_13747])).

tff(c_20,plain,(
    ! [A_7,B_8] : r1_tarski(k3_xboole_0(A_7,B_8),A_7) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_15395,plain,(
    ! [A_784,A_783] : r1_tarski(k3_xboole_0(A_784,A_783),A_783) ),
    inference(superposition,[status(thm),theory(equality)],[c_13858,c_20])).

tff(c_42,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_32,plain,(
    ! [A_19,B_20] :
      ( m1_subset_1(A_19,k1_zfmisc_1(B_20))
      | ~ r1_tarski(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_70,plain,(
    ! [B_44,A_45] :
      ( v1_relat_1(B_44)
      | ~ m1_subset_1(B_44,k1_zfmisc_1(A_45))
      | ~ v1_relat_1(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_75,plain,(
    ! [A_46,B_47] :
      ( v1_relat_1(A_46)
      | ~ v1_relat_1(B_47)
      | ~ r1_tarski(A_46,B_47) ) ),
    inference(resolution,[status(thm)],[c_32,c_70])).

tff(c_79,plain,(
    ! [A_7,B_8] :
      ( v1_relat_1(k3_xboole_0(A_7,B_8))
      | ~ v1_relat_1(A_7) ) ),
    inference(resolution,[status(thm)],[c_20,c_75])).

tff(c_40,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_36,plain,(
    ! [A_24,B_26] :
      ( r1_tarski(k3_relat_1(A_24),k3_relat_1(B_26))
      | ~ r1_tarski(A_24,B_26)
      | ~ v1_relat_1(B_26)
      | ~ v1_relat_1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_99,plain,(
    ! [A_56,B_57,C_58] :
      ( r1_tarski(A_56,k3_xboole_0(B_57,C_58))
      | ~ r1_tarski(A_56,C_58)
      | ~ r1_tarski(A_56,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_38,plain,(
    ~ r1_tarski(k3_relat_1(k3_xboole_0('#skF_3','#skF_4')),k3_xboole_0(k3_relat_1('#skF_3'),k3_relat_1('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_107,plain,
    ( ~ r1_tarski(k3_relat_1(k3_xboole_0('#skF_3','#skF_4')),k3_relat_1('#skF_4'))
    | ~ r1_tarski(k3_relat_1(k3_xboole_0('#skF_3','#skF_4')),k3_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_99,c_38])).

tff(c_118,plain,(
    ~ r1_tarski(k3_relat_1(k3_xboole_0('#skF_3','#skF_4')),k3_relat_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_107])).

tff(c_121,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_3','#skF_4'),'#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_36,c_118])).

tff(c_124,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_20,c_121])).

tff(c_127,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_79,c_124])).

tff(c_131,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_127])).

tff(c_132,plain,(
    ~ r1_tarski(k3_relat_1(k3_xboole_0('#skF_3','#skF_4')),k3_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_107])).

tff(c_136,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_3','#skF_4'),'#skF_4')
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_36,c_132])).

tff(c_139,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_3','#skF_4'),'#skF_4')
    | ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_136])).

tff(c_166,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_139])).

tff(c_169,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_79,c_166])).

tff(c_173,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_169])).

tff(c_174,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_3','#skF_4'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_139])).

tff(c_15902,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_15395,c_174])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:37:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.94/4.39  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.94/4.40  
% 11.94/4.40  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.94/4.40  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k3_relat_1 > k1_zfmisc_1 > k1_setfam_1 > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 11.94/4.40  
% 11.94/4.40  %Foreground sorts:
% 11.94/4.40  
% 11.94/4.40  
% 11.94/4.40  %Background operators:
% 11.94/4.40  
% 11.94/4.40  
% 11.94/4.40  %Foreground operators:
% 11.94/4.40  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 11.94/4.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.94/4.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 11.94/4.40  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 11.94/4.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.94/4.40  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 11.94/4.40  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 11.94/4.40  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 11.94/4.40  tff('#skF_3', type, '#skF_3': $i).
% 11.94/4.40  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 11.94/4.40  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 11.94/4.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.94/4.40  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 11.94/4.40  tff('#skF_4', type, '#skF_4': $i).
% 11.94/4.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.94/4.40  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 11.94/4.40  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 11.94/4.40  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 11.94/4.40  
% 11.94/4.42  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 11.94/4.42  tff(f_36, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 11.94/4.42  tff(f_76, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k3_relat_1(k3_xboole_0(A, B)), k3_xboole_0(k3_relat_1(A), k3_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_relat_1)).
% 11.94/4.42  tff(f_52, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 11.94/4.42  tff(f_59, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 11.94/4.42  tff(f_68, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => r1_tarski(k3_relat_1(A), k3_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_relat_1)).
% 11.94/4.42  tff(f_42, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_xboole_1)).
% 11.94/4.42  tff(c_16, plain, (![A_1, B_2, C_3]: (r2_hidden('#skF_1'(A_1, B_2, C_3), B_2) | r2_hidden('#skF_2'(A_1, B_2, C_3), C_3) | k3_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_34])).
% 11.94/4.42  tff(c_186, plain, (![A_71, B_72, C_73]: (~r2_hidden('#skF_1'(A_71, B_72, C_73), C_73) | r2_hidden('#skF_2'(A_71, B_72, C_73), C_73) | k3_xboole_0(A_71, B_72)=C_73)), inference(cnfTransformation, [status(thm)], [f_34])).
% 11.94/4.42  tff(c_195, plain, (![A_1, B_2]: (r2_hidden('#skF_2'(A_1, B_2, B_2), B_2) | k3_xboole_0(A_1, B_2)=B_2)), inference(resolution, [status(thm)], [c_16, c_186])).
% 11.94/4.42  tff(c_145, plain, (![A_66, B_67, C_68]: (r2_hidden('#skF_1'(A_66, B_67, C_68), B_67) | r2_hidden('#skF_2'(A_66, B_67, C_68), C_68) | k3_xboole_0(A_66, B_67)=C_68)), inference(cnfTransformation, [status(thm)], [f_34])).
% 11.94/4.42  tff(c_4, plain, (![D_6, B_2, A_1]: (r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k3_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 11.94/4.42  tff(c_492, plain, (![A_109, B_110, A_111, B_112]: (r2_hidden('#skF_2'(A_109, B_110, k3_xboole_0(A_111, B_112)), B_112) | r2_hidden('#skF_1'(A_109, B_110, k3_xboole_0(A_111, B_112)), B_110) | k3_xboole_0(A_111, B_112)=k3_xboole_0(A_109, B_110))), inference(resolution, [status(thm)], [c_145, c_4])).
% 11.94/4.42  tff(c_10, plain, (![A_1, B_2, C_3]: (r2_hidden('#skF_1'(A_1, B_2, C_3), B_2) | ~r2_hidden('#skF_2'(A_1, B_2, C_3), B_2) | ~r2_hidden('#skF_2'(A_1, B_2, C_3), A_1) | k3_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_34])).
% 11.94/4.42  tff(c_526, plain, (![B_112, B_110, A_111]: (~r2_hidden('#skF_2'(B_112, B_110, k3_xboole_0(A_111, B_112)), B_110) | r2_hidden('#skF_1'(B_112, B_110, k3_xboole_0(A_111, B_112)), B_110) | k3_xboole_0(B_112, B_110)=k3_xboole_0(A_111, B_112))), inference(resolution, [status(thm)], [c_492, c_10])).
% 11.94/4.42  tff(c_208, plain, (![A_76, B_77, C_78]: (r2_hidden('#skF_1'(A_76, B_77, C_78), A_76) | r2_hidden('#skF_2'(A_76, B_77, C_78), C_78) | k3_xboole_0(A_76, B_77)=C_78)), inference(cnfTransformation, [status(thm)], [f_34])).
% 11.94/4.42  tff(c_14, plain, (![A_1, B_2, C_3]: (~r2_hidden('#skF_1'(A_1, B_2, C_3), C_3) | r2_hidden('#skF_2'(A_1, B_2, C_3), C_3) | k3_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_34])).
% 11.94/4.42  tff(c_229, plain, (![A_76, B_77]: (r2_hidden('#skF_2'(A_76, B_77, A_76), A_76) | k3_xboole_0(A_76, B_77)=A_76)), inference(resolution, [status(thm)], [c_208, c_14])).
% 11.94/4.42  tff(c_18, plain, (![A_1, B_2, C_3]: (r2_hidden('#skF_1'(A_1, B_2, C_3), A_1) | r2_hidden('#skF_2'(A_1, B_2, C_3), C_3) | k3_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_34])).
% 11.94/4.42  tff(c_330, plain, (![A_98, B_99, C_100]: (r2_hidden('#skF_1'(A_98, B_99, C_100), A_98) | ~r2_hidden('#skF_2'(A_98, B_99, C_100), B_99) | ~r2_hidden('#skF_2'(A_98, B_99, C_100), A_98) | k3_xboole_0(A_98, B_99)=C_100)), inference(cnfTransformation, [status(thm)], [f_34])).
% 11.94/4.42  tff(c_352, plain, (![A_1, C_3]: (~r2_hidden('#skF_2'(A_1, C_3, C_3), A_1) | r2_hidden('#skF_1'(A_1, C_3, C_3), A_1) | k3_xboole_0(A_1, C_3)=C_3)), inference(resolution, [status(thm)], [c_18, c_330])).
% 11.94/4.42  tff(c_371, plain, (![A_103, B_104, C_105]: (~r2_hidden('#skF_1'(A_103, B_104, C_105), C_105) | ~r2_hidden('#skF_2'(A_103, B_104, C_105), B_104) | ~r2_hidden('#skF_2'(A_103, B_104, C_105), A_103) | k3_xboole_0(A_103, B_104)=C_105)), inference(cnfTransformation, [status(thm)], [f_34])).
% 11.94/4.42  tff(c_392, plain, (![A_106]: (~r2_hidden('#skF_2'(A_106, A_106, A_106), A_106) | k3_xboole_0(A_106, A_106)=A_106)), inference(resolution, [status(thm)], [c_352, c_371])).
% 11.94/4.42  tff(c_409, plain, (![B_77]: (k3_xboole_0(B_77, B_77)=B_77)), inference(resolution, [status(thm)], [c_229, c_392])).
% 11.94/4.42  tff(c_6, plain, (![D_6, A_1, B_2]: (r2_hidden(D_6, A_1) | ~r2_hidden(D_6, k3_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 11.94/4.42  tff(c_535, plain, (![A_113, B_114, A_115, B_116]: (r2_hidden('#skF_2'(A_113, B_114, k3_xboole_0(A_115, B_116)), A_115) | r2_hidden('#skF_1'(A_113, B_114, k3_xboole_0(A_115, B_116)), B_114) | k3_xboole_0(A_115, B_116)=k3_xboole_0(A_113, B_114))), inference(resolution, [status(thm)], [c_145, c_6])).
% 11.94/4.42  tff(c_574, plain, (![A_113, B_2, A_1, A_115, B_116]: (r2_hidden('#skF_1'(A_113, k3_xboole_0(A_1, B_2), k3_xboole_0(A_115, B_116)), B_2) | r2_hidden('#skF_2'(A_113, k3_xboole_0(A_1, B_2), k3_xboole_0(A_115, B_116)), A_115) | k3_xboole_0(A_115, B_116)=k3_xboole_0(A_113, k3_xboole_0(A_1, B_2)))), inference(resolution, [status(thm)], [c_535, c_4])).
% 11.94/4.42  tff(c_575, plain, (![A_113, B_2, A_1, A_115, B_116]: (r2_hidden('#skF_1'(A_113, k3_xboole_0(A_1, B_2), k3_xboole_0(A_115, B_116)), A_1) | r2_hidden('#skF_2'(A_113, k3_xboole_0(A_1, B_2), k3_xboole_0(A_115, B_116)), A_115) | k3_xboole_0(A_115, B_116)=k3_xboole_0(A_113, k3_xboole_0(A_1, B_2)))), inference(resolution, [status(thm)], [c_535, c_6])).
% 11.94/4.42  tff(c_2, plain, (![D_6, A_1, B_2]: (r2_hidden(D_6, k3_xboole_0(A_1, B_2)) | ~r2_hidden(D_6, B_2) | ~r2_hidden(D_6, A_1))), inference(cnfTransformation, [status(thm)], [f_34])).
% 11.94/4.42  tff(c_905, plain, (![A_150, B_151, A_152, B_153]: (r2_hidden('#skF_2'(A_150, B_151, k3_xboole_0(A_152, B_153)), k3_xboole_0(A_152, B_153)) | k3_xboole_0(A_152, B_153)=k3_xboole_0(A_150, B_151) | ~r2_hidden('#skF_1'(A_150, B_151, k3_xboole_0(A_152, B_153)), B_153) | ~r2_hidden('#skF_1'(A_150, B_151, k3_xboole_0(A_152, B_153)), A_152))), inference(resolution, [status(thm)], [c_2, c_186])).
% 11.94/4.42  tff(c_6505, plain, (![A_566, B_567, A_568, B_569]: (r2_hidden('#skF_2'(A_566, B_567, k3_xboole_0(A_568, B_569)), A_568) | k3_xboole_0(A_568, B_569)=k3_xboole_0(A_566, B_567) | ~r2_hidden('#skF_1'(A_566, B_567, k3_xboole_0(A_568, B_569)), B_569) | ~r2_hidden('#skF_1'(A_566, B_567, k3_xboole_0(A_568, B_569)), A_568))), inference(resolution, [status(thm)], [c_905, c_6])).
% 11.94/4.42  tff(c_9578, plain, (![A_707, A_708, B_709, A_710]: (~r2_hidden('#skF_1'(A_707, k3_xboole_0(A_708, B_709), k3_xboole_0(A_710, A_708)), A_710) | r2_hidden('#skF_2'(A_707, k3_xboole_0(A_708, B_709), k3_xboole_0(A_710, A_708)), A_710) | k3_xboole_0(A_710, A_708)=k3_xboole_0(A_707, k3_xboole_0(A_708, B_709)))), inference(resolution, [status(thm)], [c_575, c_6505])).
% 11.94/4.42  tff(c_9992, plain, (![A_715, B_716, B_717]: (r2_hidden('#skF_2'(A_715, k3_xboole_0(B_716, B_717), k3_xboole_0(B_717, B_716)), B_717) | k3_xboole_0(A_715, k3_xboole_0(B_716, B_717))=k3_xboole_0(B_717, B_716))), inference(resolution, [status(thm)], [c_574, c_9578])).
% 11.94/4.42  tff(c_10039, plain, (![A_715, B_716, A_1, B_2]: (r2_hidden('#skF_2'(A_715, k3_xboole_0(B_716, k3_xboole_0(A_1, B_2)), k3_xboole_0(k3_xboole_0(A_1, B_2), B_716)), B_2) | k3_xboole_0(A_715, k3_xboole_0(B_716, k3_xboole_0(A_1, B_2)))=k3_xboole_0(k3_xboole_0(A_1, B_2), B_716))), inference(resolution, [status(thm)], [c_9992, c_4])).
% 11.94/4.42  tff(c_2343, plain, (![A_263, B_264, A_265, B_266]: (~r2_hidden('#skF_2'(A_263, B_264, k3_xboole_0(A_265, B_266)), B_264) | ~r2_hidden('#skF_2'(A_263, B_264, k3_xboole_0(A_265, B_266)), A_263) | k3_xboole_0(A_265, B_266)=k3_xboole_0(A_263, B_264) | ~r2_hidden('#skF_1'(A_263, B_264, k3_xboole_0(A_265, B_266)), B_266) | ~r2_hidden('#skF_1'(A_263, B_264, k3_xboole_0(A_265, B_266)), A_265))), inference(resolution, [status(thm)], [c_2, c_371])).
% 11.94/4.42  tff(c_11139, plain, (![A_768, A_769, B_770]: (~r2_hidden('#skF_2'(A_768, k3_xboole_0(A_769, B_770), k3_xboole_0(A_769, B_770)), A_768) | ~r2_hidden('#skF_1'(A_768, k3_xboole_0(A_769, B_770), k3_xboole_0(A_769, B_770)), B_770) | ~r2_hidden('#skF_1'(A_768, k3_xboole_0(A_769, B_770), k3_xboole_0(A_769, B_770)), A_769) | k3_xboole_0(A_768, k3_xboole_0(A_769, B_770))=k3_xboole_0(A_769, B_770))), inference(resolution, [status(thm)], [c_195, c_2343])).
% 11.94/4.42  tff(c_11145, plain, (![B_2, A_1]: (~r2_hidden('#skF_1'(B_2, k3_xboole_0(k3_xboole_0(A_1, B_2), k3_xboole_0(A_1, B_2)), k3_xboole_0(k3_xboole_0(A_1, B_2), k3_xboole_0(A_1, B_2))), k3_xboole_0(A_1, B_2)) | k3_xboole_0(B_2, k3_xboole_0(k3_xboole_0(A_1, B_2), k3_xboole_0(A_1, B_2)))=k3_xboole_0(k3_xboole_0(A_1, B_2), k3_xboole_0(A_1, B_2)))), inference(resolution, [status(thm)], [c_10039, c_11139])).
% 11.94/4.42  tff(c_11418, plain, (![B_773, A_774]: (~r2_hidden('#skF_1'(B_773, k3_xboole_0(A_774, B_773), k3_xboole_0(A_774, B_773)), k3_xboole_0(A_774, B_773)) | k3_xboole_0(B_773, k3_xboole_0(A_774, B_773))=k3_xboole_0(A_774, B_773))), inference(demodulation, [status(thm), theory('equality')], [c_409, c_409, c_409, c_409, c_11145])).
% 11.94/4.42  tff(c_13747, plain, (![B_781, A_782]: (~r2_hidden('#skF_2'(B_781, k3_xboole_0(A_782, B_781), k3_xboole_0(A_782, B_781)), k3_xboole_0(A_782, B_781)) | k3_xboole_0(B_781, k3_xboole_0(A_782, B_781))=k3_xboole_0(A_782, B_781))), inference(resolution, [status(thm)], [c_526, c_11418])).
% 11.94/4.42  tff(c_13858, plain, (![A_783, A_784]: (k3_xboole_0(A_783, k3_xboole_0(A_784, A_783))=k3_xboole_0(A_784, A_783))), inference(resolution, [status(thm)], [c_195, c_13747])).
% 11.94/4.42  tff(c_20, plain, (![A_7, B_8]: (r1_tarski(k3_xboole_0(A_7, B_8), A_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 11.94/4.42  tff(c_15395, plain, (![A_784, A_783]: (r1_tarski(k3_xboole_0(A_784, A_783), A_783))), inference(superposition, [status(thm), theory('equality')], [c_13858, c_20])).
% 11.94/4.42  tff(c_42, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_76])).
% 11.94/4.42  tff(c_32, plain, (![A_19, B_20]: (m1_subset_1(A_19, k1_zfmisc_1(B_20)) | ~r1_tarski(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_52])).
% 11.94/4.42  tff(c_70, plain, (![B_44, A_45]: (v1_relat_1(B_44) | ~m1_subset_1(B_44, k1_zfmisc_1(A_45)) | ~v1_relat_1(A_45))), inference(cnfTransformation, [status(thm)], [f_59])).
% 11.94/4.42  tff(c_75, plain, (![A_46, B_47]: (v1_relat_1(A_46) | ~v1_relat_1(B_47) | ~r1_tarski(A_46, B_47))), inference(resolution, [status(thm)], [c_32, c_70])).
% 11.94/4.42  tff(c_79, plain, (![A_7, B_8]: (v1_relat_1(k3_xboole_0(A_7, B_8)) | ~v1_relat_1(A_7))), inference(resolution, [status(thm)], [c_20, c_75])).
% 11.94/4.42  tff(c_40, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_76])).
% 11.94/4.42  tff(c_36, plain, (![A_24, B_26]: (r1_tarski(k3_relat_1(A_24), k3_relat_1(B_26)) | ~r1_tarski(A_24, B_26) | ~v1_relat_1(B_26) | ~v1_relat_1(A_24))), inference(cnfTransformation, [status(thm)], [f_68])).
% 11.94/4.42  tff(c_99, plain, (![A_56, B_57, C_58]: (r1_tarski(A_56, k3_xboole_0(B_57, C_58)) | ~r1_tarski(A_56, C_58) | ~r1_tarski(A_56, B_57))), inference(cnfTransformation, [status(thm)], [f_42])).
% 11.94/4.42  tff(c_38, plain, (~r1_tarski(k3_relat_1(k3_xboole_0('#skF_3', '#skF_4')), k3_xboole_0(k3_relat_1('#skF_3'), k3_relat_1('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_76])).
% 11.94/4.42  tff(c_107, plain, (~r1_tarski(k3_relat_1(k3_xboole_0('#skF_3', '#skF_4')), k3_relat_1('#skF_4')) | ~r1_tarski(k3_relat_1(k3_xboole_0('#skF_3', '#skF_4')), k3_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_99, c_38])).
% 11.94/4.42  tff(c_118, plain, (~r1_tarski(k3_relat_1(k3_xboole_0('#skF_3', '#skF_4')), k3_relat_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_107])).
% 11.94/4.42  tff(c_121, plain, (~r1_tarski(k3_xboole_0('#skF_3', '#skF_4'), '#skF_3') | ~v1_relat_1('#skF_3') | ~v1_relat_1(k3_xboole_0('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_36, c_118])).
% 11.94/4.42  tff(c_124, plain, (~v1_relat_1(k3_xboole_0('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_20, c_121])).
% 11.94/4.42  tff(c_127, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_79, c_124])).
% 11.94/4.42  tff(c_131, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_127])).
% 11.94/4.42  tff(c_132, plain, (~r1_tarski(k3_relat_1(k3_xboole_0('#skF_3', '#skF_4')), k3_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_107])).
% 11.94/4.42  tff(c_136, plain, (~r1_tarski(k3_xboole_0('#skF_3', '#skF_4'), '#skF_4') | ~v1_relat_1('#skF_4') | ~v1_relat_1(k3_xboole_0('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_36, c_132])).
% 11.94/4.42  tff(c_139, plain, (~r1_tarski(k3_xboole_0('#skF_3', '#skF_4'), '#skF_4') | ~v1_relat_1(k3_xboole_0('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_136])).
% 11.94/4.42  tff(c_166, plain, (~v1_relat_1(k3_xboole_0('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_139])).
% 11.94/4.42  tff(c_169, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_79, c_166])).
% 11.94/4.42  tff(c_173, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_169])).
% 11.94/4.42  tff(c_174, plain, (~r1_tarski(k3_xboole_0('#skF_3', '#skF_4'), '#skF_4')), inference(splitRight, [status(thm)], [c_139])).
% 11.94/4.42  tff(c_15902, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_15395, c_174])).
% 11.94/4.42  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.94/4.42  
% 11.94/4.42  Inference rules
% 11.94/4.42  ----------------------
% 11.94/4.42  #Ref     : 0
% 11.94/4.42  #Sup     : 3423
% 11.94/4.42  #Fact    : 0
% 11.94/4.42  #Define  : 0
% 11.94/4.42  #Split   : 3
% 11.94/4.42  #Chain   : 0
% 11.94/4.42  #Close   : 0
% 11.94/4.42  
% 11.94/4.42  Ordering : KBO
% 11.94/4.42  
% 11.94/4.42  Simplification rules
% 11.94/4.42  ----------------------
% 11.94/4.42  #Subsume      : 1902
% 11.94/4.42  #Demod        : 4659
% 11.94/4.42  #Tautology    : 346
% 11.94/4.42  #SimpNegUnit  : 0
% 11.94/4.42  #BackRed      : 5
% 11.94/4.42  
% 11.94/4.42  #Partial instantiations: 0
% 11.94/4.42  #Strategies tried      : 1
% 11.94/4.42  
% 11.94/4.42  Timing (in seconds)
% 11.94/4.42  ----------------------
% 11.94/4.42  Preprocessing        : 0.33
% 11.94/4.43  Parsing              : 0.17
% 11.94/4.43  CNF conversion       : 0.03
% 11.94/4.43  Main loop            : 3.27
% 11.94/4.43  Inferencing          : 1.04
% 11.94/4.43  Reduction            : 0.77
% 11.94/4.43  Demodulation         : 0.57
% 11.94/4.43  BG Simplification    : 0.09
% 11.94/4.43  Subsumption          : 1.21
% 11.94/4.43  Abstraction          : 0.24
% 11.94/4.43  MUC search           : 0.00
% 11.94/4.43  Cooper               : 0.00
% 11.94/4.43  Total                : 3.64
% 11.94/4.43  Index Insertion      : 0.00
% 11.94/4.43  Index Deletion       : 0.00
% 11.94/4.43  Index Matching       : 0.00
% 11.94/4.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
