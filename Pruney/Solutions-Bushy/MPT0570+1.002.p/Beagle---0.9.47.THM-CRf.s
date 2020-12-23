%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0570+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:31 EST 2020

% Result     : Theorem 29.97s
% Output     : CNFRefutation 29.97s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 131 expanded)
%              Number of leaves         :   33 (  59 expanded)
%              Depth                    :   13
%              Number of atoms          :  122 ( 255 expanded)
%              Number of equality atoms :   12 (  30 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k4_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_3 > #skF_5 > #skF_9 > #skF_7 > #skF_8 > #skF_2 > #skF_1 > #skF_6 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_6',type,(
    '#skF_6': $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_43,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_94,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ~ ( A != k1_xboole_0
            & r1_tarski(A,k2_relat_1(B))
            & k10_relat_1(B,A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t174_relat_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_75,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

tff(f_40,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).

tff(c_22,plain,(
    ! [A_25] : m1_subset_1('#skF_6'(A_25),A_25) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_48,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_46,plain,(
    r1_tarski('#skF_8',k2_relat_1('#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_32,plain,(
    ! [A_33,B_34] :
      ( r2_hidden(A_33,B_34)
      | v1_xboole_0(B_34)
      | ~ m1_subset_1(A_33,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_115,plain,(
    ! [C_65,B_66,A_67] :
      ( r2_hidden(C_65,B_66)
      | ~ r2_hidden(C_65,A_67)
      | ~ r1_tarski(A_67,B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_244,plain,(
    ! [A_98,B_99,B_100] :
      ( r2_hidden(A_98,B_99)
      | ~ r1_tarski(B_100,B_99)
      | v1_xboole_0(B_100)
      | ~ m1_subset_1(A_98,B_100) ) ),
    inference(resolution,[status(thm)],[c_32,c_115])).

tff(c_262,plain,(
    ! [A_98] :
      ( r2_hidden(A_98,k2_relat_1('#skF_9'))
      | v1_xboole_0('#skF_8')
      | ~ m1_subset_1(A_98,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_46,c_244])).

tff(c_341,plain,(
    v1_xboole_0('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_262])).

tff(c_40,plain,(
    ! [A_40] :
      ( k1_xboole_0 = A_40
      | ~ v1_xboole_0(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_346,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_341,c_40])).

tff(c_351,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_346])).

tff(c_352,plain,(
    ! [A_98] :
      ( r2_hidden(A_98,k2_relat_1('#skF_9'))
      | ~ m1_subset_1(A_98,'#skF_8') ) ),
    inference(splitRight,[status(thm)],[c_262])).

tff(c_353,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(splitRight,[status(thm)],[c_262])).

tff(c_20,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_55,plain,(
    ! [A_43] :
      ( k1_xboole_0 = A_43
      | ~ v1_xboole_0(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_59,plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_55])).

tff(c_60,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_20])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_89,plain,(
    ! [A_56,B_57] :
      ( ~ r2_hidden('#skF_1'(A_56,B_57),B_57)
      | r1_tarski(A_56,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_98,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_89])).

tff(c_263,plain,(
    ! [A_101,C_102] :
      ( r2_hidden(k4_tarski('#skF_5'(A_101,k2_relat_1(A_101),C_102),C_102),A_101)
      | ~ r2_hidden(C_102,k2_relat_1(A_101)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_36,plain,(
    ! [A_35,B_36] :
      ( m1_subset_1(A_35,k1_zfmisc_1(B_36))
      | ~ r1_tarski(A_35,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_107,plain,(
    ! [C_62,B_63,A_64] :
      ( ~ v1_xboole_0(C_62)
      | ~ m1_subset_1(B_63,k1_zfmisc_1(C_62))
      | ~ r2_hidden(A_64,B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_113,plain,(
    ! [B_36,A_64,A_35] :
      ( ~ v1_xboole_0(B_36)
      | ~ r2_hidden(A_64,A_35)
      | ~ r1_tarski(A_35,B_36) ) ),
    inference(resolution,[status(thm)],[c_36,c_107])).

tff(c_319,plain,(
    ! [B_107,A_108,C_109] :
      ( ~ v1_xboole_0(B_107)
      | ~ r1_tarski(A_108,B_107)
      | ~ r2_hidden(C_109,k2_relat_1(A_108)) ) ),
    inference(resolution,[status(thm)],[c_263,c_113])).

tff(c_354,plain,(
    ! [A_110,C_111] :
      ( ~ v1_xboole_0(A_110)
      | ~ r2_hidden(C_111,k2_relat_1(A_110)) ) ),
    inference(resolution,[status(thm)],[c_98,c_319])).

tff(c_662,plain,(
    ! [A_140,A_141] :
      ( ~ v1_xboole_0(A_140)
      | v1_xboole_0(k2_relat_1(A_140))
      | ~ m1_subset_1(A_141,k2_relat_1(A_140)) ) ),
    inference(resolution,[status(thm)],[c_32,c_354])).

tff(c_667,plain,(
    ! [A_142] :
      ( ~ v1_xboole_0(A_142)
      | v1_xboole_0(k2_relat_1(A_142)) ) ),
    inference(resolution,[status(thm)],[c_22,c_662])).

tff(c_679,plain,(
    ! [A_143] :
      ( k2_relat_1(A_143) = k1_xboole_0
      | ~ v1_xboole_0(A_143) ) ),
    inference(resolution,[status(thm)],[c_667,c_40])).

tff(c_687,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_60,c_679])).

tff(c_338,plain,(
    ! [A_1,C_109] :
      ( ~ v1_xboole_0(A_1)
      | ~ r2_hidden(C_109,k2_relat_1(A_1)) ) ),
    inference(resolution,[status(thm)],[c_98,c_319])).

tff(c_717,plain,(
    ! [C_109] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(C_109,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_687,c_338])).

tff(c_740,plain,(
    ! [C_109] : ~ r2_hidden(C_109,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_717])).

tff(c_50,plain,(
    v1_relat_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_44,plain,(
    k10_relat_1('#skF_9','#skF_8') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_8,plain,(
    ! [A_6,C_21] :
      ( r2_hidden(k4_tarski('#skF_5'(A_6,k2_relat_1(A_6),C_21),C_21),A_6)
      | ~ r2_hidden(C_21,k2_relat_1(A_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1796,plain,(
    ! [A_187,C_188,B_189,D_190] :
      ( r2_hidden(A_187,k10_relat_1(C_188,B_189))
      | ~ r2_hidden(D_190,B_189)
      | ~ r2_hidden(k4_tarski(A_187,D_190),C_188)
      | ~ r2_hidden(D_190,k2_relat_1(C_188))
      | ~ v1_relat_1(C_188) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_16381,plain,(
    ! [A_390,C_391,B_392,A_393] :
      ( r2_hidden(A_390,k10_relat_1(C_391,B_392))
      | ~ r2_hidden(k4_tarski(A_390,A_393),C_391)
      | ~ r2_hidden(A_393,k2_relat_1(C_391))
      | ~ v1_relat_1(C_391)
      | v1_xboole_0(B_392)
      | ~ m1_subset_1(A_393,B_392) ) ),
    inference(resolution,[status(thm)],[c_32,c_1796])).

tff(c_136989,plain,(
    ! [A_1103,C_1104,B_1105] :
      ( r2_hidden('#skF_5'(A_1103,k2_relat_1(A_1103),C_1104),k10_relat_1(A_1103,B_1105))
      | ~ v1_relat_1(A_1103)
      | v1_xboole_0(B_1105)
      | ~ m1_subset_1(C_1104,B_1105)
      | ~ r2_hidden(C_1104,k2_relat_1(A_1103)) ) ),
    inference(resolution,[status(thm)],[c_8,c_16381])).

tff(c_137341,plain,(
    ! [C_1104] :
      ( r2_hidden('#skF_5'('#skF_9',k2_relat_1('#skF_9'),C_1104),k1_xboole_0)
      | ~ v1_relat_1('#skF_9')
      | v1_xboole_0('#skF_8')
      | ~ m1_subset_1(C_1104,'#skF_8')
      | ~ r2_hidden(C_1104,k2_relat_1('#skF_9')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_136989])).

tff(c_137468,plain,(
    ! [C_1104] :
      ( r2_hidden('#skF_5'('#skF_9',k2_relat_1('#skF_9'),C_1104),k1_xboole_0)
      | v1_xboole_0('#skF_8')
      | ~ m1_subset_1(C_1104,'#skF_8')
      | ~ r2_hidden(C_1104,k2_relat_1('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_137341])).

tff(c_137470,plain,(
    ! [C_1106] :
      ( ~ m1_subset_1(C_1106,'#skF_8')
      | ~ r2_hidden(C_1106,k2_relat_1('#skF_9')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_353,c_740,c_137468])).

tff(c_137684,plain,(
    ! [A_1107] : ~ m1_subset_1(A_1107,'#skF_8') ),
    inference(resolution,[status(thm)],[c_352,c_137470])).

tff(c_137689,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_22,c_137684])).

%------------------------------------------------------------------------------
