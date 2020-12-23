%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0832+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:55 EST 2020

% Result     : Theorem 4.46s
% Output     : CNFRefutation 4.46s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 247 expanded)
%              Number of leaves         :   30 (  98 expanded)
%              Depth                    :   17
%              Number of atoms          :  184 ( 505 expanded)
%              Number of equality atoms :   20 (  60 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k6_relset_1 > k8_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > #skF_6 > #skF_1 > #skF_4 > #skF_7 > #skF_10 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k6_relset_1,type,(
    k6_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_79,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,A)))
       => m1_subset_1(k6_relset_1(C,A,B,D),k1_zfmisc_1(k2_zfmisc_1(C,B))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_relset_1)).

tff(f_64,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k6_relset_1(A,B,C,D) = k8_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_relset_1)).

tff(f_56,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k6_relset_1(A,B,C,D),k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relset_1)).

tff(f_28,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_52,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_tarski(A,B)
        <=> ! [C,D] :
              ( r2_hidden(k4_tarski(C,D),A)
             => r2_hidden(k4_tarski(C,D),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_relat_1)).

tff(f_70,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_zfmisc_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => ( C = k8_relat_1(A,B)
          <=> ! [D,E] :
                ( r2_hidden(k4_tarski(D,E),C)
              <=> ( r2_hidden(E,A)
                  & r2_hidden(k4_tarski(D,E),B) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_relat_1)).

tff(c_46,plain,(
    m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_9','#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_89,plain,(
    ! [A_79,B_80,C_81,D_82] :
      ( k6_relset_1(A_79,B_80,C_81,D_82) = k8_relat_1(C_81,D_82)
      | ~ m1_subset_1(D_82,k1_zfmisc_1(k2_zfmisc_1(A_79,B_80))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_96,plain,(
    ! [C_81] : k6_relset_1('#skF_9','#skF_7',C_81,'#skF_10') = k8_relat_1(C_81,'#skF_10') ),
    inference(resolution,[status(thm)],[c_46,c_89])).

tff(c_162,plain,(
    ! [A_101,B_102,C_103,D_104] :
      ( m1_subset_1(k6_relset_1(A_101,B_102,C_103,D_104),k1_zfmisc_1(k2_zfmisc_1(A_101,B_102)))
      | ~ m1_subset_1(D_104,k1_zfmisc_1(k2_zfmisc_1(A_101,B_102))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_173,plain,(
    ! [C_81] :
      ( m1_subset_1(k8_relat_1(C_81,'#skF_10'),k1_zfmisc_1(k2_zfmisc_1('#skF_9','#skF_7')))
      | ~ m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_9','#skF_7'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_162])).

tff(c_179,plain,(
    ! [C_105] : m1_subset_1(k8_relat_1(C_105,'#skF_10'),k1_zfmisc_1(k2_zfmisc_1('#skF_9','#skF_7'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_173])).

tff(c_2,plain,(
    ! [C_3,A_1,B_2] :
      ( v1_relat_1(C_3)
      | ~ m1_subset_1(C_3,k1_zfmisc_1(k2_zfmisc_1(A_1,B_2))) ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_189,plain,(
    ! [C_105] : v1_relat_1(k8_relat_1(C_105,'#skF_10')) ),
    inference(resolution,[status(thm)],[c_179,c_2])).

tff(c_40,plain,(
    ! [A_53,B_54] :
      ( r1_tarski(A_53,B_54)
      | ~ m1_subset_1(A_53,k1_zfmisc_1(B_54)) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_190,plain,(
    ! [C_105] : r1_tarski(k8_relat_1(C_105,'#skF_10'),k2_zfmisc_1('#skF_9','#skF_7')) ),
    inference(resolution,[status(thm)],[c_179,c_40])).

tff(c_26,plain,(
    ! [A_22,B_32] :
      ( r2_hidden(k4_tarski('#skF_5'(A_22,B_32),'#skF_6'(A_22,B_32)),A_22)
      | r1_tarski(A_22,B_32)
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_149,plain,(
    ! [C_93,D_94,B_95,A_96] :
      ( r2_hidden(k4_tarski(C_93,D_94),B_95)
      | ~ r2_hidden(k4_tarski(C_93,D_94),A_96)
      | ~ r1_tarski(A_96,B_95)
      | ~ v1_relat_1(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_571,plain,(
    ! [A_218,B_219,B_220] :
      ( r2_hidden(k4_tarski('#skF_5'(A_218,B_219),'#skF_6'(A_218,B_219)),B_220)
      | ~ r1_tarski(A_218,B_220)
      | r1_tarski(A_218,B_219)
      | ~ v1_relat_1(A_218) ) ),
    inference(resolution,[status(thm)],[c_26,c_149])).

tff(c_38,plain,(
    ! [A_49,C_51,B_50,D_52] :
      ( r2_hidden(A_49,C_51)
      | ~ r2_hidden(k4_tarski(A_49,B_50),k2_zfmisc_1(C_51,D_52)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_635,plain,(
    ! [A_228,B_229,C_230,D_231] :
      ( r2_hidden('#skF_5'(A_228,B_229),C_230)
      | ~ r1_tarski(A_228,k2_zfmisc_1(C_230,D_231))
      | r1_tarski(A_228,B_229)
      | ~ v1_relat_1(A_228) ) ),
    inference(resolution,[status(thm)],[c_571,c_38])).

tff(c_645,plain,(
    ! [C_105,B_229] :
      ( r2_hidden('#skF_5'(k8_relat_1(C_105,'#skF_10'),B_229),'#skF_9')
      | r1_tarski(k8_relat_1(C_105,'#skF_10'),B_229)
      | ~ v1_relat_1(k8_relat_1(C_105,'#skF_10')) ) ),
    inference(resolution,[status(thm)],[c_190,c_635])).

tff(c_663,plain,(
    ! [C_105,B_229] :
      ( r2_hidden('#skF_5'(k8_relat_1(C_105,'#skF_10'),B_229),'#skF_9')
      | r1_tarski(k8_relat_1(C_105,'#skF_10'),B_229) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_189,c_645])).

tff(c_58,plain,(
    ! [C_61,A_62,B_63] :
      ( v1_relat_1(C_61)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_62,B_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_67,plain,(
    v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_46,c_58])).

tff(c_32,plain,(
    ! [A_45,B_46,C_47,D_48] :
      ( k6_relset_1(A_45,B_46,C_47,D_48) = k8_relat_1(C_47,D_48)
      | ~ m1_subset_1(D_48,k1_zfmisc_1(k2_zfmisc_1(A_45,B_46))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_188,plain,(
    ! [C_47,C_105] : k6_relset_1('#skF_9','#skF_7',C_47,k8_relat_1(C_105,'#skF_10')) = k8_relat_1(C_47,k8_relat_1(C_105,'#skF_10')) ),
    inference(resolution,[status(thm)],[c_179,c_32])).

tff(c_178,plain,(
    ! [C_81] : m1_subset_1(k8_relat_1(C_81,'#skF_10'),k1_zfmisc_1(k2_zfmisc_1('#skF_9','#skF_7'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_173])).

tff(c_207,plain,(
    ! [A_112,B_113,C_114,D_115] :
      ( v1_relat_1(k6_relset_1(A_112,B_113,C_114,D_115))
      | ~ m1_subset_1(D_115,k1_zfmisc_1(k2_zfmisc_1(A_112,B_113))) ) ),
    inference(resolution,[status(thm)],[c_162,c_2])).

tff(c_217,plain,(
    ! [C_114,C_81] : v1_relat_1(k6_relset_1('#skF_9','#skF_7',C_114,k8_relat_1(C_81,'#skF_10'))) ),
    inference(resolution,[status(thm)],[c_178,c_207])).

tff(c_236,plain,(
    ! [C_114,C_81] : v1_relat_1(k8_relat_1(C_114,k8_relat_1(C_81,'#skF_10'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_188,c_217])).

tff(c_518,plain,(
    ! [A_215,B_216,C_217] :
      ( r2_hidden(k4_tarski('#skF_1'(A_215,B_216,C_217),'#skF_2'(A_215,B_216,C_217)),B_216)
      | r2_hidden(k4_tarski('#skF_3'(A_215,B_216,C_217),'#skF_4'(A_215,B_216,C_217)),C_217)
      | k8_relat_1(A_215,B_216) = C_217
      | ~ v1_relat_1(C_217)
      | ~ v1_relat_1(B_216) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_10,plain,(
    ! [A_4,B_5,C_15] :
      ( ~ r2_hidden(k4_tarski('#skF_1'(A_4,B_5,C_15),'#skF_2'(A_4,B_5,C_15)),C_15)
      | r2_hidden(k4_tarski('#skF_3'(A_4,B_5,C_15),'#skF_4'(A_4,B_5,C_15)),C_15)
      | k8_relat_1(A_4,B_5) = C_15
      | ~ v1_relat_1(C_15)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_690,plain,(
    ! [A_244,B_245] :
      ( r2_hidden(k4_tarski('#skF_3'(A_244,B_245,B_245),'#skF_4'(A_244,B_245,B_245)),B_245)
      | k8_relat_1(A_244,B_245) = B_245
      | ~ v1_relat_1(B_245) ) ),
    inference(resolution,[status(thm)],[c_518,c_10])).

tff(c_22,plain,(
    ! [C_37,D_38,B_32,A_22] :
      ( r2_hidden(k4_tarski(C_37,D_38),B_32)
      | ~ r2_hidden(k4_tarski(C_37,D_38),A_22)
      | ~ r1_tarski(A_22,B_32)
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_727,plain,(
    ! [A_262,B_263,B_264] :
      ( r2_hidden(k4_tarski('#skF_3'(A_262,B_263,B_263),'#skF_4'(A_262,B_263,B_263)),B_264)
      | ~ r1_tarski(B_263,B_264)
      | k8_relat_1(A_262,B_263) = B_263
      | ~ v1_relat_1(B_263) ) ),
    inference(resolution,[status(thm)],[c_690,c_22])).

tff(c_36,plain,(
    ! [B_50,D_52,A_49,C_51] :
      ( r2_hidden(B_50,D_52)
      | ~ r2_hidden(k4_tarski(A_49,B_50),k2_zfmisc_1(C_51,D_52)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_785,plain,(
    ! [A_268,B_269,D_270,C_271] :
      ( r2_hidden('#skF_4'(A_268,B_269,B_269),D_270)
      | ~ r1_tarski(B_269,k2_zfmisc_1(C_271,D_270))
      | k8_relat_1(A_268,B_269) = B_269
      | ~ v1_relat_1(B_269) ) ),
    inference(resolution,[status(thm)],[c_727,c_36])).

tff(c_795,plain,(
    ! [A_268,C_105] :
      ( r2_hidden('#skF_4'(A_268,k8_relat_1(C_105,'#skF_10'),k8_relat_1(C_105,'#skF_10')),'#skF_7')
      | k8_relat_1(A_268,k8_relat_1(C_105,'#skF_10')) = k8_relat_1(C_105,'#skF_10')
      | ~ v1_relat_1(k8_relat_1(C_105,'#skF_10')) ) ),
    inference(resolution,[status(thm)],[c_190,c_785])).

tff(c_813,plain,(
    ! [A_268,C_105] :
      ( r2_hidden('#skF_4'(A_268,k8_relat_1(C_105,'#skF_10'),k8_relat_1(C_105,'#skF_10')),'#skF_7')
      | k8_relat_1(A_268,k8_relat_1(C_105,'#skF_10')) = k8_relat_1(C_105,'#skF_10') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_189,c_795])).

tff(c_559,plain,(
    ! [A_215,B_216] :
      ( r2_hidden(k4_tarski('#skF_3'(A_215,B_216,B_216),'#skF_4'(A_215,B_216,B_216)),B_216)
      | k8_relat_1(A_215,B_216) = B_216
      | ~ v1_relat_1(B_216) ) ),
    inference(resolution,[status(thm)],[c_518,c_10])).

tff(c_6,plain,(
    ! [A_4,B_5,C_15] :
      ( r2_hidden(k4_tarski('#skF_1'(A_4,B_5,C_15),'#skF_2'(A_4,B_5,C_15)),B_5)
      | ~ r2_hidden(k4_tarski('#skF_3'(A_4,B_5,C_15),'#skF_4'(A_4,B_5,C_15)),B_5)
      | ~ r2_hidden('#skF_4'(A_4,B_5,C_15),A_4)
      | k8_relat_1(A_4,B_5) = C_15
      | ~ v1_relat_1(C_15)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1015,plain,(
    ! [A_284,B_285,C_286] :
      ( ~ r2_hidden(k4_tarski('#skF_1'(A_284,B_285,C_286),'#skF_2'(A_284,B_285,C_286)),C_286)
      | ~ r2_hidden(k4_tarski('#skF_3'(A_284,B_285,C_286),'#skF_4'(A_284,B_285,C_286)),B_285)
      | ~ r2_hidden('#skF_4'(A_284,B_285,C_286),A_284)
      | k8_relat_1(A_284,B_285) = C_286
      | ~ v1_relat_1(C_286)
      | ~ v1_relat_1(B_285) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1291,plain,(
    ! [A_340,B_341] :
      ( ~ r2_hidden(k4_tarski('#skF_3'(A_340,B_341,B_341),'#skF_4'(A_340,B_341,B_341)),B_341)
      | ~ r2_hidden('#skF_4'(A_340,B_341,B_341),A_340)
      | k8_relat_1(A_340,B_341) = B_341
      | ~ v1_relat_1(B_341) ) ),
    inference(resolution,[status(thm)],[c_6,c_1015])).

tff(c_1318,plain,(
    ! [A_342,B_343] :
      ( ~ r2_hidden('#skF_4'(A_342,B_343,B_343),A_342)
      | k8_relat_1(A_342,B_343) = B_343
      | ~ v1_relat_1(B_343) ) ),
    inference(resolution,[status(thm)],[c_559,c_1291])).

tff(c_1330,plain,(
    ! [C_105] :
      ( ~ v1_relat_1(k8_relat_1(C_105,'#skF_10'))
      | k8_relat_1('#skF_7',k8_relat_1(C_105,'#skF_10')) = k8_relat_1(C_105,'#skF_10') ) ),
    inference(resolution,[status(thm)],[c_813,c_1318])).

tff(c_1347,plain,(
    ! [C_105] : k8_relat_1('#skF_7',k8_relat_1(C_105,'#skF_10')) = k8_relat_1(C_105,'#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_189,c_1330])).

tff(c_191,plain,(
    ! [D_106,E_107,B_108,A_109] :
      ( r2_hidden(k4_tarski(D_106,E_107),B_108)
      | ~ r2_hidden(k4_tarski(D_106,E_107),k8_relat_1(A_109,B_108))
      | ~ v1_relat_1(k8_relat_1(A_109,B_108))
      | ~ v1_relat_1(B_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1705,plain,(
    ! [A_361,B_362,B_363] :
      ( r2_hidden(k4_tarski('#skF_5'(k8_relat_1(A_361,B_362),B_363),'#skF_6'(k8_relat_1(A_361,B_362),B_363)),B_362)
      | ~ v1_relat_1(B_362)
      | r1_tarski(k8_relat_1(A_361,B_362),B_363)
      | ~ v1_relat_1(k8_relat_1(A_361,B_362)) ) ),
    inference(resolution,[status(thm)],[c_26,c_191])).

tff(c_24,plain,(
    ! [A_22,B_32] :
      ( ~ r2_hidden(k4_tarski('#skF_5'(A_22,B_32),'#skF_6'(A_22,B_32)),B_32)
      | r1_tarski(A_22,B_32)
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_1785,plain,(
    ! [B_364,A_365] :
      ( ~ v1_relat_1(B_364)
      | r1_tarski(k8_relat_1(A_365,B_364),B_364)
      | ~ v1_relat_1(k8_relat_1(A_365,B_364)) ) ),
    inference(resolution,[status(thm)],[c_1705,c_24])).

tff(c_1823,plain,(
    ! [C_105] :
      ( ~ v1_relat_1(k8_relat_1(C_105,'#skF_10'))
      | r1_tarski(k8_relat_1(C_105,'#skF_10'),k8_relat_1(C_105,'#skF_10'))
      | ~ v1_relat_1(k8_relat_1('#skF_7',k8_relat_1(C_105,'#skF_10'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1347,c_1785])).

tff(c_1853,plain,(
    ! [C_366] : r1_tarski(k8_relat_1(C_366,'#skF_10'),k8_relat_1(C_366,'#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_236,c_189,c_1823])).

tff(c_20,plain,(
    ! [E_21,A_4,D_20,B_5] :
      ( r2_hidden(E_21,A_4)
      | ~ r2_hidden(k4_tarski(D_20,E_21),k8_relat_1(A_4,B_5))
      | ~ v1_relat_1(k8_relat_1(A_4,B_5))
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_595,plain,(
    ! [A_218,B_219,A_4,B_5] :
      ( r2_hidden('#skF_6'(A_218,B_219),A_4)
      | ~ v1_relat_1(k8_relat_1(A_4,B_5))
      | ~ v1_relat_1(B_5)
      | ~ r1_tarski(A_218,k8_relat_1(A_4,B_5))
      | r1_tarski(A_218,B_219)
      | ~ v1_relat_1(A_218) ) ),
    inference(resolution,[status(thm)],[c_571,c_20])).

tff(c_1857,plain,(
    ! [C_366,B_219] :
      ( r2_hidden('#skF_6'(k8_relat_1(C_366,'#skF_10'),B_219),C_366)
      | ~ v1_relat_1('#skF_10')
      | r1_tarski(k8_relat_1(C_366,'#skF_10'),B_219)
      | ~ v1_relat_1(k8_relat_1(C_366,'#skF_10')) ) ),
    inference(resolution,[status(thm)],[c_1853,c_595])).

tff(c_1911,plain,(
    ! [C_370,B_371] :
      ( r2_hidden('#skF_6'(k8_relat_1(C_370,'#skF_10'),B_371),C_370)
      | r1_tarski(k8_relat_1(C_370,'#skF_10'),B_371) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_189,c_67,c_1857])).

tff(c_34,plain,(
    ! [A_49,B_50,C_51,D_52] :
      ( r2_hidden(k4_tarski(A_49,B_50),k2_zfmisc_1(C_51,D_52))
      | ~ r2_hidden(B_50,D_52)
      | ~ r2_hidden(A_49,C_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_128,plain,(
    ! [A_90,B_91] :
      ( ~ r2_hidden(k4_tarski('#skF_5'(A_90,B_91),'#skF_6'(A_90,B_91)),B_91)
      | r1_tarski(A_90,B_91)
      | ~ v1_relat_1(A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_138,plain,(
    ! [A_90,C_51,D_52] :
      ( r1_tarski(A_90,k2_zfmisc_1(C_51,D_52))
      | ~ v1_relat_1(A_90)
      | ~ r2_hidden('#skF_6'(A_90,k2_zfmisc_1(C_51,D_52)),D_52)
      | ~ r2_hidden('#skF_5'(A_90,k2_zfmisc_1(C_51,D_52)),C_51) ) ),
    inference(resolution,[status(thm)],[c_34,c_128])).

tff(c_1914,plain,(
    ! [C_370,C_51] :
      ( ~ v1_relat_1(k8_relat_1(C_370,'#skF_10'))
      | ~ r2_hidden('#skF_5'(k8_relat_1(C_370,'#skF_10'),k2_zfmisc_1(C_51,C_370)),C_51)
      | r1_tarski(k8_relat_1(C_370,'#skF_10'),k2_zfmisc_1(C_51,C_370)) ) ),
    inference(resolution,[status(thm)],[c_1911,c_138])).

tff(c_2258,plain,(
    ! [C_398,C_399] :
      ( ~ r2_hidden('#skF_5'(k8_relat_1(C_398,'#skF_10'),k2_zfmisc_1(C_399,C_398)),C_399)
      | r1_tarski(k8_relat_1(C_398,'#skF_10'),k2_zfmisc_1(C_399,C_398)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_189,c_1914])).

tff(c_2267,plain,(
    ! [C_105] : r1_tarski(k8_relat_1(C_105,'#skF_10'),k2_zfmisc_1('#skF_9',C_105)) ),
    inference(resolution,[status(thm)],[c_663,c_2258])).

tff(c_42,plain,(
    ! [A_53,B_54] :
      ( m1_subset_1(A_53,k1_zfmisc_1(B_54))
      | ~ r1_tarski(A_53,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_44,plain,(
    ~ m1_subset_1(k6_relset_1('#skF_9','#skF_7','#skF_8','#skF_10'),k1_zfmisc_1(k2_zfmisc_1('#skF_9','#skF_8'))) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_78,plain,(
    ~ r1_tarski(k6_relset_1('#skF_9','#skF_7','#skF_8','#skF_10'),k2_zfmisc_1('#skF_9','#skF_8')) ),
    inference(resolution,[status(thm)],[c_42,c_44])).

tff(c_97,plain,(
    ~ r1_tarski(k8_relat_1('#skF_8','#skF_10'),k2_zfmisc_1('#skF_9','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_78])).

tff(c_2270,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2267,c_97])).

%------------------------------------------------------------------------------
