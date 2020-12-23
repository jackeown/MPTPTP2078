%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:48 EST 2020

% Result     : Theorem 3.40s
% Output     : CNFRefutation 3.50s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 499 expanded)
%              Number of leaves         :   18 ( 187 expanded)
%              Depth                    :   26
%              Number of atoms          :  167 (1230 expanded)
%              Number of equality atoms :   22 ( 355 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > k7_setfam_1 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k7_setfam_1,type,(
    k7_setfam_1: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_67,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ~ ( B != k1_xboole_0
            & k7_setfam_1(A,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_setfam_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A)))
         => ( C = k7_setfam_1(A,B)
          <=> ! [D] :
                ( m1_subset_1(D,k1_zfmisc_1(A))
               => ( r2_hidden(D,C)
                <=> r2_hidden(k3_subset_1(A,D),B) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_setfam_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k7_setfam_1(A,k7_setfam_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).

tff(f_34,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_32,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(c_26,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_28,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_24,plain,(
    k7_setfam_1('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_6,plain,(
    ! [A_6,B_7,C_13] :
      ( m1_subset_1('#skF_1'(A_6,B_7,C_13),k1_zfmisc_1(A_6))
      | k7_setfam_1(A_6,B_7) = C_13
      | ~ m1_subset_1(C_13,k1_zfmisc_1(k1_zfmisc_1(A_6)))
      | ~ m1_subset_1(B_7,k1_zfmisc_1(k1_zfmisc_1(A_6))) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_14,plain,(
    ! [A_6,B_7,C_13] :
      ( r2_hidden('#skF_1'(A_6,B_7,C_13),C_13)
      | r2_hidden(k3_subset_1(A_6,'#skF_1'(A_6,B_7,C_13)),B_7)
      | k7_setfam_1(A_6,B_7) = C_13
      | ~ m1_subset_1(C_13,k1_zfmisc_1(k1_zfmisc_1(A_6)))
      | ~ m1_subset_1(B_7,k1_zfmisc_1(k1_zfmisc_1(A_6))) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_48,plain,(
    ! [A_34,B_35] :
      ( k7_setfam_1(A_34,k7_setfam_1(A_34,B_35)) = B_35
      | ~ m1_subset_1(B_35,k1_zfmisc_1(k1_zfmisc_1(A_34))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_50,plain,(
    k7_setfam_1('#skF_2',k7_setfam_1('#skF_2','#skF_3')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_28,c_48])).

tff(c_55,plain,(
    k7_setfam_1('#skF_2',k1_xboole_0) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_50])).

tff(c_4,plain,(
    ! [A_5] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_34,plain,(
    ! [A_23,C_24,B_25] :
      ( m1_subset_1(A_23,C_24)
      | ~ m1_subset_1(B_25,k1_zfmisc_1(C_24))
      | ~ r2_hidden(A_23,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_39,plain,(
    ! [A_23] :
      ( m1_subset_1(A_23,k1_zfmisc_1('#skF_2'))
      | ~ r2_hidden(A_23,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_28,c_34])).

tff(c_81,plain,(
    ! [A_44,D_45,B_46] :
      ( r2_hidden(k3_subset_1(A_44,D_45),B_46)
      | ~ r2_hidden(D_45,k7_setfam_1(A_44,B_46))
      | ~ m1_subset_1(D_45,k1_zfmisc_1(A_44))
      | ~ m1_subset_1(k7_setfam_1(A_44,B_46),k1_zfmisc_1(k1_zfmisc_1(A_44)))
      | ~ m1_subset_1(B_46,k1_zfmisc_1(k1_zfmisc_1(A_44))) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_85,plain,(
    ! [D_45] :
      ( r2_hidden(k3_subset_1('#skF_2',D_45),k1_xboole_0)
      | ~ r2_hidden(D_45,k7_setfam_1('#skF_2',k1_xboole_0))
      | ~ m1_subset_1(D_45,k1_zfmisc_1('#skF_2'))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_2')))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_55,c_81])).

tff(c_107,plain,(
    ! [D_51] :
      ( r2_hidden(k3_subset_1('#skF_2',D_51),k1_xboole_0)
      | ~ r2_hidden(D_51,'#skF_3')
      | ~ m1_subset_1(D_51,k1_zfmisc_1('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_28,c_55,c_85])).

tff(c_2,plain,(
    ! [C_4,A_1,B_2] :
      ( r2_hidden(C_4,A_1)
      | ~ r2_hidden(C_4,B_2)
      | ~ m1_subset_1(B_2,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_115,plain,(
    ! [D_51,A_1] :
      ( r2_hidden(k3_subset_1('#skF_2',D_51),A_1)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_1))
      | ~ r2_hidden(D_51,'#skF_3')
      | ~ m1_subset_1(D_51,k1_zfmisc_1('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_107,c_2])).

tff(c_134,plain,(
    ! [D_54,A_55] :
      ( r2_hidden(k3_subset_1('#skF_2',D_54),A_55)
      | ~ r2_hidden(D_54,'#skF_3')
      | ~ m1_subset_1(D_54,k1_zfmisc_1('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_115])).

tff(c_16,plain,(
    ! [D_16,A_6,B_7] :
      ( r2_hidden(D_16,k7_setfam_1(A_6,B_7))
      | ~ r2_hidden(k3_subset_1(A_6,D_16),B_7)
      | ~ m1_subset_1(D_16,k1_zfmisc_1(A_6))
      | ~ m1_subset_1(k7_setfam_1(A_6,B_7),k1_zfmisc_1(k1_zfmisc_1(A_6)))
      | ~ m1_subset_1(B_7,k1_zfmisc_1(k1_zfmisc_1(A_6))) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_310,plain,(
    ! [D_78,A_79] :
      ( r2_hidden(D_78,k7_setfam_1('#skF_2',A_79))
      | ~ m1_subset_1(k7_setfam_1('#skF_2',A_79),k1_zfmisc_1(k1_zfmisc_1('#skF_2')))
      | ~ m1_subset_1(A_79,k1_zfmisc_1(k1_zfmisc_1('#skF_2')))
      | ~ r2_hidden(D_78,'#skF_3')
      | ~ m1_subset_1(D_78,k1_zfmisc_1('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_134,c_16])).

tff(c_320,plain,(
    ! [D_78] :
      ( r2_hidden(D_78,k7_setfam_1('#skF_2','#skF_3'))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1('#skF_2')))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_2')))
      | ~ r2_hidden(D_78,'#skF_3')
      | ~ m1_subset_1(D_78,k1_zfmisc_1('#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_310])).

tff(c_327,plain,(
    ! [D_80] :
      ( r2_hidden(D_80,k1_xboole_0)
      | ~ r2_hidden(D_80,'#skF_3')
      | ~ m1_subset_1(D_80,k1_zfmisc_1('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_4,c_24,c_320])).

tff(c_352,plain,(
    ! [A_81] :
      ( r2_hidden(A_81,k1_xboole_0)
      | ~ r2_hidden(A_81,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_39,c_327])).

tff(c_358,plain,(
    ! [D_16,A_6] :
      ( r2_hidden(D_16,k7_setfam_1(A_6,k1_xboole_0))
      | ~ m1_subset_1(D_16,k1_zfmisc_1(A_6))
      | ~ m1_subset_1(k7_setfam_1(A_6,k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(A_6)))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(A_6)))
      | ~ r2_hidden(k3_subset_1(A_6,D_16),'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_352,c_16])).

tff(c_575,plain,(
    ! [D_102,A_103] :
      ( r2_hidden(D_102,k7_setfam_1(A_103,k1_xboole_0))
      | ~ m1_subset_1(D_102,k1_zfmisc_1(A_103))
      | ~ m1_subset_1(k7_setfam_1(A_103,k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(A_103)))
      | ~ r2_hidden(k3_subset_1(A_103,D_102),'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_358])).

tff(c_577,plain,(
    ! [D_102] :
      ( r2_hidden(D_102,k7_setfam_1('#skF_2',k1_xboole_0))
      | ~ m1_subset_1(D_102,k1_zfmisc_1('#skF_2'))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_2')))
      | ~ r2_hidden(k3_subset_1('#skF_2',D_102),'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_55,c_575])).

tff(c_580,plain,(
    ! [D_104] :
      ( r2_hidden(D_104,'#skF_3')
      | ~ m1_subset_1(D_104,k1_zfmisc_1('#skF_2'))
      | ~ r2_hidden(k3_subset_1('#skF_2',D_104),'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_55,c_577])).

tff(c_592,plain,(
    ! [C_13] :
      ( r2_hidden('#skF_1'('#skF_2','#skF_3',C_13),'#skF_3')
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_3',C_13),k1_zfmisc_1('#skF_2'))
      | r2_hidden('#skF_1'('#skF_2','#skF_3',C_13),C_13)
      | k7_setfam_1('#skF_2','#skF_3') = C_13
      | ~ m1_subset_1(C_13,k1_zfmisc_1(k1_zfmisc_1('#skF_2')))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_14,c_580])).

tff(c_852,plain,(
    ! [C_125] :
      ( r2_hidden('#skF_1'('#skF_2','#skF_3',C_125),'#skF_3')
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_3',C_125),k1_zfmisc_1('#skF_2'))
      | r2_hidden('#skF_1'('#skF_2','#skF_3',C_125),C_125)
      | k1_xboole_0 = C_125
      | ~ m1_subset_1(C_125,k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_24,c_592])).

tff(c_855,plain,(
    ! [C_13] :
      ( r2_hidden('#skF_1'('#skF_2','#skF_3',C_13),'#skF_3')
      | r2_hidden('#skF_1'('#skF_2','#skF_3',C_13),C_13)
      | k1_xboole_0 = C_13
      | k7_setfam_1('#skF_2','#skF_3') = C_13
      | ~ m1_subset_1(C_13,k1_zfmisc_1(k1_zfmisc_1('#skF_2')))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_6,c_852])).

tff(c_859,plain,(
    ! [C_126] :
      ( r2_hidden('#skF_1'('#skF_2','#skF_3',C_126),'#skF_3')
      | r2_hidden('#skF_1'('#skF_2','#skF_3',C_126),C_126)
      | k1_xboole_0 = C_126
      | ~ m1_subset_1(C_126,k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_24,c_855])).

tff(c_876,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_3','#skF_3'),'#skF_3')
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_28,c_859])).

tff(c_887,plain,(
    r2_hidden('#skF_1'('#skF_2','#skF_3','#skF_3'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_876])).

tff(c_40,plain,(
    ! [A_23,A_5] :
      ( m1_subset_1(A_23,A_5)
      | ~ r2_hidden(A_23,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_4,c_34])).

tff(c_372,plain,(
    ! [A_81,A_5] :
      ( m1_subset_1(A_81,A_5)
      | ~ r2_hidden(A_81,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_352,c_40])).

tff(c_924,plain,(
    ! [A_5] : m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_3'),A_5) ),
    inference(resolution,[status(thm)],[c_887,c_372])).

tff(c_364,plain,(
    ! [A_81,A_1] :
      ( r2_hidden(A_81,A_1)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_1))
      | ~ r2_hidden(A_81,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_352,c_2])).

tff(c_375,plain,(
    ! [A_81,A_1] :
      ( r2_hidden(A_81,A_1)
      | ~ r2_hidden(A_81,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_364])).

tff(c_923,plain,(
    ! [A_1] : r2_hidden('#skF_1'('#skF_2','#skF_3','#skF_3'),A_1) ),
    inference(resolution,[status(thm)],[c_887,c_375])).

tff(c_928,plain,(
    ! [A_130] : r2_hidden('#skF_1'('#skF_2','#skF_3','#skF_3'),A_130) ),
    inference(resolution,[status(thm)],[c_887,c_375])).

tff(c_87,plain,(
    ! [D_45] :
      ( r2_hidden(k3_subset_1('#skF_2',D_45),'#skF_3')
      | ~ r2_hidden(D_45,k7_setfam_1('#skF_2','#skF_3'))
      | ~ m1_subset_1(D_45,k1_zfmisc_1('#skF_2'))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1('#skF_2')))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_81])).

tff(c_93,plain,(
    ! [D_45] :
      ( r2_hidden(k3_subset_1('#skF_2',D_45),'#skF_3')
      | ~ r2_hidden(D_45,k1_xboole_0)
      | ~ m1_subset_1(D_45,k1_zfmisc_1('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_4,c_24,c_87])).

tff(c_259,plain,(
    ! [A_70,B_71,C_72] :
      ( ~ r2_hidden(k3_subset_1(A_70,'#skF_1'(A_70,B_71,C_72)),B_71)
      | ~ r2_hidden('#skF_1'(A_70,B_71,C_72),C_72)
      | k7_setfam_1(A_70,B_71) = C_72
      | ~ m1_subset_1(C_72,k1_zfmisc_1(k1_zfmisc_1(A_70)))
      | ~ m1_subset_1(B_71,k1_zfmisc_1(k1_zfmisc_1(A_70))) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_270,plain,(
    ! [C_72] :
      ( ~ r2_hidden('#skF_1'('#skF_2','#skF_3',C_72),C_72)
      | k7_setfam_1('#skF_2','#skF_3') = C_72
      | ~ m1_subset_1(C_72,k1_zfmisc_1(k1_zfmisc_1('#skF_2')))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_2')))
      | ~ r2_hidden('#skF_1'('#skF_2','#skF_3',C_72),k1_xboole_0)
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_3',C_72),k1_zfmisc_1('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_93,c_259])).

tff(c_276,plain,(
    ! [C_72] :
      ( ~ r2_hidden('#skF_1'('#skF_2','#skF_3',C_72),C_72)
      | k1_xboole_0 = C_72
      | ~ m1_subset_1(C_72,k1_zfmisc_1(k1_zfmisc_1('#skF_2')))
      | ~ r2_hidden('#skF_1'('#skF_2','#skF_3',C_72),k1_xboole_0)
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_3',C_72),k1_zfmisc_1('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_24,c_270])).

tff(c_934,plain,
    ( k1_xboole_0 = '#skF_3'
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_2')))
    | ~ r2_hidden('#skF_1'('#skF_2','#skF_3','#skF_3'),k1_xboole_0)
    | ~ m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_3'),k1_zfmisc_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_928,c_276])).

tff(c_960,plain,
    ( k1_xboole_0 = '#skF_3'
    | ~ m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_3'),k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_923,c_28,c_934])).

tff(c_961,plain,(
    ~ m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_3'),k1_zfmisc_1('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_960])).

tff(c_1001,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_924,c_961])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:41:22 EST 2020
% 0.12/0.35  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.40/1.55  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.40/1.56  
% 3.40/1.56  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.40/1.56  %$ r2_hidden > m1_subset_1 > k7_setfam_1 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3
% 3.40/1.56  
% 3.40/1.56  %Foreground sorts:
% 3.40/1.56  
% 3.40/1.56  
% 3.40/1.56  %Background operators:
% 3.40/1.56  
% 3.40/1.56  
% 3.40/1.56  %Foreground operators:
% 3.40/1.56  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.40/1.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.40/1.56  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.40/1.56  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.40/1.56  tff(k7_setfam_1, type, k7_setfam_1: ($i * $i) > $i).
% 3.40/1.56  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.40/1.56  tff('#skF_2', type, '#skF_2': $i).
% 3.40/1.56  tff('#skF_3', type, '#skF_3': $i).
% 3.40/1.56  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.40/1.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.40/1.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.40/1.56  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.40/1.56  
% 3.50/1.57  tff(f_67, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => ~(~(B = k1_xboole_0) & (k7_setfam_1(A, B) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_setfam_1)).
% 3.50/1.57  tff(f_48, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => ((C = k7_setfam_1(A, B)) <=> (![D]: (m1_subset_1(D, k1_zfmisc_1(A)) => (r2_hidden(D, C) <=> r2_hidden(k3_subset_1(A, D), B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_setfam_1)).
% 3.50/1.57  tff(f_52, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k7_setfam_1(A, k7_setfam_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k7_setfam_1)).
% 3.50/1.57  tff(f_34, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 3.50/1.57  tff(f_58, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 3.50/1.57  tff(f_32, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 3.50/1.57  tff(c_26, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.50/1.57  tff(c_28, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.50/1.57  tff(c_24, plain, (k7_setfam_1('#skF_2', '#skF_3')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.50/1.57  tff(c_6, plain, (![A_6, B_7, C_13]: (m1_subset_1('#skF_1'(A_6, B_7, C_13), k1_zfmisc_1(A_6)) | k7_setfam_1(A_6, B_7)=C_13 | ~m1_subset_1(C_13, k1_zfmisc_1(k1_zfmisc_1(A_6))) | ~m1_subset_1(B_7, k1_zfmisc_1(k1_zfmisc_1(A_6))))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.50/1.57  tff(c_14, plain, (![A_6, B_7, C_13]: (r2_hidden('#skF_1'(A_6, B_7, C_13), C_13) | r2_hidden(k3_subset_1(A_6, '#skF_1'(A_6, B_7, C_13)), B_7) | k7_setfam_1(A_6, B_7)=C_13 | ~m1_subset_1(C_13, k1_zfmisc_1(k1_zfmisc_1(A_6))) | ~m1_subset_1(B_7, k1_zfmisc_1(k1_zfmisc_1(A_6))))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.50/1.57  tff(c_48, plain, (![A_34, B_35]: (k7_setfam_1(A_34, k7_setfam_1(A_34, B_35))=B_35 | ~m1_subset_1(B_35, k1_zfmisc_1(k1_zfmisc_1(A_34))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.50/1.57  tff(c_50, plain, (k7_setfam_1('#skF_2', k7_setfam_1('#skF_2', '#skF_3'))='#skF_3'), inference(resolution, [status(thm)], [c_28, c_48])).
% 3.50/1.57  tff(c_55, plain, (k7_setfam_1('#skF_2', k1_xboole_0)='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_24, c_50])).
% 3.50/1.57  tff(c_4, plain, (![A_5]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.50/1.57  tff(c_34, plain, (![A_23, C_24, B_25]: (m1_subset_1(A_23, C_24) | ~m1_subset_1(B_25, k1_zfmisc_1(C_24)) | ~r2_hidden(A_23, B_25))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.50/1.57  tff(c_39, plain, (![A_23]: (m1_subset_1(A_23, k1_zfmisc_1('#skF_2')) | ~r2_hidden(A_23, '#skF_3'))), inference(resolution, [status(thm)], [c_28, c_34])).
% 3.50/1.57  tff(c_81, plain, (![A_44, D_45, B_46]: (r2_hidden(k3_subset_1(A_44, D_45), B_46) | ~r2_hidden(D_45, k7_setfam_1(A_44, B_46)) | ~m1_subset_1(D_45, k1_zfmisc_1(A_44)) | ~m1_subset_1(k7_setfam_1(A_44, B_46), k1_zfmisc_1(k1_zfmisc_1(A_44))) | ~m1_subset_1(B_46, k1_zfmisc_1(k1_zfmisc_1(A_44))))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.50/1.57  tff(c_85, plain, (![D_45]: (r2_hidden(k3_subset_1('#skF_2', D_45), k1_xboole_0) | ~r2_hidden(D_45, k7_setfam_1('#skF_2', k1_xboole_0)) | ~m1_subset_1(D_45, k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1('#skF_2'))))), inference(superposition, [status(thm), theory('equality')], [c_55, c_81])).
% 3.50/1.57  tff(c_107, plain, (![D_51]: (r2_hidden(k3_subset_1('#skF_2', D_51), k1_xboole_0) | ~r2_hidden(D_51, '#skF_3') | ~m1_subset_1(D_51, k1_zfmisc_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_28, c_55, c_85])).
% 3.50/1.57  tff(c_2, plain, (![C_4, A_1, B_2]: (r2_hidden(C_4, A_1) | ~r2_hidden(C_4, B_2) | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.50/1.57  tff(c_115, plain, (![D_51, A_1]: (r2_hidden(k3_subset_1('#skF_2', D_51), A_1) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_1)) | ~r2_hidden(D_51, '#skF_3') | ~m1_subset_1(D_51, k1_zfmisc_1('#skF_2')))), inference(resolution, [status(thm)], [c_107, c_2])).
% 3.50/1.57  tff(c_134, plain, (![D_54, A_55]: (r2_hidden(k3_subset_1('#skF_2', D_54), A_55) | ~r2_hidden(D_54, '#skF_3') | ~m1_subset_1(D_54, k1_zfmisc_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_115])).
% 3.50/1.57  tff(c_16, plain, (![D_16, A_6, B_7]: (r2_hidden(D_16, k7_setfam_1(A_6, B_7)) | ~r2_hidden(k3_subset_1(A_6, D_16), B_7) | ~m1_subset_1(D_16, k1_zfmisc_1(A_6)) | ~m1_subset_1(k7_setfam_1(A_6, B_7), k1_zfmisc_1(k1_zfmisc_1(A_6))) | ~m1_subset_1(B_7, k1_zfmisc_1(k1_zfmisc_1(A_6))))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.50/1.57  tff(c_310, plain, (![D_78, A_79]: (r2_hidden(D_78, k7_setfam_1('#skF_2', A_79)) | ~m1_subset_1(k7_setfam_1('#skF_2', A_79), k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) | ~m1_subset_1(A_79, k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) | ~r2_hidden(D_78, '#skF_3') | ~m1_subset_1(D_78, k1_zfmisc_1('#skF_2')))), inference(resolution, [status(thm)], [c_134, c_16])).
% 3.50/1.57  tff(c_320, plain, (![D_78]: (r2_hidden(D_78, k7_setfam_1('#skF_2', '#skF_3')) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) | ~r2_hidden(D_78, '#skF_3') | ~m1_subset_1(D_78, k1_zfmisc_1('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_24, c_310])).
% 3.50/1.57  tff(c_327, plain, (![D_80]: (r2_hidden(D_80, k1_xboole_0) | ~r2_hidden(D_80, '#skF_3') | ~m1_subset_1(D_80, k1_zfmisc_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_4, c_24, c_320])).
% 3.50/1.57  tff(c_352, plain, (![A_81]: (r2_hidden(A_81, k1_xboole_0) | ~r2_hidden(A_81, '#skF_3'))), inference(resolution, [status(thm)], [c_39, c_327])).
% 3.50/1.57  tff(c_358, plain, (![D_16, A_6]: (r2_hidden(D_16, k7_setfam_1(A_6, k1_xboole_0)) | ~m1_subset_1(D_16, k1_zfmisc_1(A_6)) | ~m1_subset_1(k7_setfam_1(A_6, k1_xboole_0), k1_zfmisc_1(k1_zfmisc_1(A_6))) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1(A_6))) | ~r2_hidden(k3_subset_1(A_6, D_16), '#skF_3'))), inference(resolution, [status(thm)], [c_352, c_16])).
% 3.50/1.57  tff(c_575, plain, (![D_102, A_103]: (r2_hidden(D_102, k7_setfam_1(A_103, k1_xboole_0)) | ~m1_subset_1(D_102, k1_zfmisc_1(A_103)) | ~m1_subset_1(k7_setfam_1(A_103, k1_xboole_0), k1_zfmisc_1(k1_zfmisc_1(A_103))) | ~r2_hidden(k3_subset_1(A_103, D_102), '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_358])).
% 3.50/1.57  tff(c_577, plain, (![D_102]: (r2_hidden(D_102, k7_setfam_1('#skF_2', k1_xboole_0)) | ~m1_subset_1(D_102, k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) | ~r2_hidden(k3_subset_1('#skF_2', D_102), '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_55, c_575])).
% 3.50/1.57  tff(c_580, plain, (![D_104]: (r2_hidden(D_104, '#skF_3') | ~m1_subset_1(D_104, k1_zfmisc_1('#skF_2')) | ~r2_hidden(k3_subset_1('#skF_2', D_104), '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_55, c_577])).
% 3.50/1.57  tff(c_592, plain, (![C_13]: (r2_hidden('#skF_1'('#skF_2', '#skF_3', C_13), '#skF_3') | ~m1_subset_1('#skF_1'('#skF_2', '#skF_3', C_13), k1_zfmisc_1('#skF_2')) | r2_hidden('#skF_1'('#skF_2', '#skF_3', C_13), C_13) | k7_setfam_1('#skF_2', '#skF_3')=C_13 | ~m1_subset_1(C_13, k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_2'))))), inference(resolution, [status(thm)], [c_14, c_580])).
% 3.50/1.57  tff(c_852, plain, (![C_125]: (r2_hidden('#skF_1'('#skF_2', '#skF_3', C_125), '#skF_3') | ~m1_subset_1('#skF_1'('#skF_2', '#skF_3', C_125), k1_zfmisc_1('#skF_2')) | r2_hidden('#skF_1'('#skF_2', '#skF_3', C_125), C_125) | k1_xboole_0=C_125 | ~m1_subset_1(C_125, k1_zfmisc_1(k1_zfmisc_1('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_24, c_592])).
% 3.50/1.57  tff(c_855, plain, (![C_13]: (r2_hidden('#skF_1'('#skF_2', '#skF_3', C_13), '#skF_3') | r2_hidden('#skF_1'('#skF_2', '#skF_3', C_13), C_13) | k1_xboole_0=C_13 | k7_setfam_1('#skF_2', '#skF_3')=C_13 | ~m1_subset_1(C_13, k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_2'))))), inference(resolution, [status(thm)], [c_6, c_852])).
% 3.50/1.57  tff(c_859, plain, (![C_126]: (r2_hidden('#skF_1'('#skF_2', '#skF_3', C_126), '#skF_3') | r2_hidden('#skF_1'('#skF_2', '#skF_3', C_126), C_126) | k1_xboole_0=C_126 | ~m1_subset_1(C_126, k1_zfmisc_1(k1_zfmisc_1('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_24, c_855])).
% 3.50/1.57  tff(c_876, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3', '#skF_3'), '#skF_3') | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_28, c_859])).
% 3.50/1.57  tff(c_887, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3', '#skF_3'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_26, c_876])).
% 3.50/1.57  tff(c_40, plain, (![A_23, A_5]: (m1_subset_1(A_23, A_5) | ~r2_hidden(A_23, k1_xboole_0))), inference(resolution, [status(thm)], [c_4, c_34])).
% 3.50/1.57  tff(c_372, plain, (![A_81, A_5]: (m1_subset_1(A_81, A_5) | ~r2_hidden(A_81, '#skF_3'))), inference(resolution, [status(thm)], [c_352, c_40])).
% 3.50/1.57  tff(c_924, plain, (![A_5]: (m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_3'), A_5))), inference(resolution, [status(thm)], [c_887, c_372])).
% 3.50/1.57  tff(c_364, plain, (![A_81, A_1]: (r2_hidden(A_81, A_1) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_1)) | ~r2_hidden(A_81, '#skF_3'))), inference(resolution, [status(thm)], [c_352, c_2])).
% 3.50/1.57  tff(c_375, plain, (![A_81, A_1]: (r2_hidden(A_81, A_1) | ~r2_hidden(A_81, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_364])).
% 3.50/1.57  tff(c_923, plain, (![A_1]: (r2_hidden('#skF_1'('#skF_2', '#skF_3', '#skF_3'), A_1))), inference(resolution, [status(thm)], [c_887, c_375])).
% 3.50/1.57  tff(c_928, plain, (![A_130]: (r2_hidden('#skF_1'('#skF_2', '#skF_3', '#skF_3'), A_130))), inference(resolution, [status(thm)], [c_887, c_375])).
% 3.50/1.57  tff(c_87, plain, (![D_45]: (r2_hidden(k3_subset_1('#skF_2', D_45), '#skF_3') | ~r2_hidden(D_45, k7_setfam_1('#skF_2', '#skF_3')) | ~m1_subset_1(D_45, k1_zfmisc_1('#skF_2')) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_2'))))), inference(superposition, [status(thm), theory('equality')], [c_24, c_81])).
% 3.50/1.57  tff(c_93, plain, (![D_45]: (r2_hidden(k3_subset_1('#skF_2', D_45), '#skF_3') | ~r2_hidden(D_45, k1_xboole_0) | ~m1_subset_1(D_45, k1_zfmisc_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_4, c_24, c_87])).
% 3.50/1.57  tff(c_259, plain, (![A_70, B_71, C_72]: (~r2_hidden(k3_subset_1(A_70, '#skF_1'(A_70, B_71, C_72)), B_71) | ~r2_hidden('#skF_1'(A_70, B_71, C_72), C_72) | k7_setfam_1(A_70, B_71)=C_72 | ~m1_subset_1(C_72, k1_zfmisc_1(k1_zfmisc_1(A_70))) | ~m1_subset_1(B_71, k1_zfmisc_1(k1_zfmisc_1(A_70))))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.50/1.57  tff(c_270, plain, (![C_72]: (~r2_hidden('#skF_1'('#skF_2', '#skF_3', C_72), C_72) | k7_setfam_1('#skF_2', '#skF_3')=C_72 | ~m1_subset_1(C_72, k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) | ~r2_hidden('#skF_1'('#skF_2', '#skF_3', C_72), k1_xboole_0) | ~m1_subset_1('#skF_1'('#skF_2', '#skF_3', C_72), k1_zfmisc_1('#skF_2')))), inference(resolution, [status(thm)], [c_93, c_259])).
% 3.50/1.57  tff(c_276, plain, (![C_72]: (~r2_hidden('#skF_1'('#skF_2', '#skF_3', C_72), C_72) | k1_xboole_0=C_72 | ~m1_subset_1(C_72, k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) | ~r2_hidden('#skF_1'('#skF_2', '#skF_3', C_72), k1_xboole_0) | ~m1_subset_1('#skF_1'('#skF_2', '#skF_3', C_72), k1_zfmisc_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_24, c_270])).
% 3.50/1.57  tff(c_934, plain, (k1_xboole_0='#skF_3' | ~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) | ~r2_hidden('#skF_1'('#skF_2', '#skF_3', '#skF_3'), k1_xboole_0) | ~m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_3'), k1_zfmisc_1('#skF_2'))), inference(resolution, [status(thm)], [c_928, c_276])).
% 3.50/1.57  tff(c_960, plain, (k1_xboole_0='#skF_3' | ~m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_3'), k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_923, c_28, c_934])).
% 3.50/1.57  tff(c_961, plain, (~m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_3'), k1_zfmisc_1('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_26, c_960])).
% 3.50/1.57  tff(c_1001, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_924, c_961])).
% 3.50/1.57  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.50/1.57  
% 3.50/1.57  Inference rules
% 3.50/1.57  ----------------------
% 3.50/1.58  #Ref     : 0
% 3.50/1.58  #Sup     : 229
% 3.50/1.58  #Fact    : 0
% 3.50/1.58  #Define  : 0
% 3.50/1.58  #Split   : 5
% 3.50/1.58  #Chain   : 0
% 3.50/1.58  #Close   : 0
% 3.50/1.58  
% 3.50/1.58  Ordering : KBO
% 3.50/1.58  
% 3.50/1.58  Simplification rules
% 3.50/1.58  ----------------------
% 3.50/1.58  #Subsume      : 54
% 3.50/1.58  #Demod        : 88
% 3.50/1.58  #Tautology    : 29
% 3.50/1.58  #SimpNegUnit  : 3
% 3.50/1.58  #BackRed      : 0
% 3.50/1.58  
% 3.50/1.58  #Partial instantiations: 0
% 3.50/1.58  #Strategies tried      : 1
% 3.50/1.58  
% 3.50/1.58  Timing (in seconds)
% 3.50/1.58  ----------------------
% 3.50/1.58  Preprocessing        : 0.29
% 3.50/1.58  Parsing              : 0.15
% 3.50/1.58  CNF conversion       : 0.02
% 3.50/1.58  Main loop            : 0.48
% 3.50/1.58  Inferencing          : 0.16
% 3.50/1.58  Reduction            : 0.12
% 3.50/1.58  Demodulation         : 0.08
% 3.50/1.58  BG Simplification    : 0.02
% 3.50/1.58  Subsumption          : 0.14
% 3.50/1.58  Abstraction          : 0.03
% 3.50/1.58  MUC search           : 0.00
% 3.50/1.58  Cooper               : 0.00
% 3.50/1.58  Total                : 0.79
% 3.50/1.58  Index Insertion      : 0.00
% 3.50/1.58  Index Deletion       : 0.00
% 3.50/1.58  Index Matching       : 0.00
% 3.50/1.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
