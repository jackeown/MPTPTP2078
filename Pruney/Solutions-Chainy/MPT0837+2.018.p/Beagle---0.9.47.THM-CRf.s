%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:07 EST 2020

% Result     : Theorem 4.05s
% Output     : CNFRefutation 4.65s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 286 expanded)
%              Number of leaves         :   44 ( 114 expanded)
%              Depth                    :   14
%              Number of atoms          :  178 ( 606 expanded)
%              Number of equality atoms :   24 (  58 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k4_xboole_0 > k4_tarski > k3_subset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_11 > #skF_6 > #skF_3 > #skF_10 > #skF_13 > #skF_2 > #skF_9 > #skF_7 > #skF_8 > #skF_5 > #skF_12 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_13',type,(
    '#skF_13': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_114,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
               => ! [D] :
                    ( r2_hidden(D,k2_relset_1(B,A,C))
                  <=> ? [E] :
                        ( m1_subset_1(E,B)
                        & r2_hidden(k4_tarski(E,D),C) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_relset_1)).

tff(f_95,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_68,axiom,(
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
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_91,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k1_relset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_relset_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_66,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

tff(c_60,plain,(
    m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_9','#skF_8'))) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_1023,plain,(
    ! [A_209,B_210,C_211] :
      ( k2_relset_1(A_209,B_210,C_211) = k2_relat_1(C_211)
      | ~ m1_subset_1(C_211,k1_zfmisc_1(k2_zfmisc_1(A_209,B_210))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_1032,plain,(
    k2_relset_1('#skF_9','#skF_8','#skF_10') = k2_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_60,c_1023])).

tff(c_76,plain,
    ( m1_subset_1('#skF_12','#skF_9')
    | r2_hidden('#skF_13',k2_relset_1('#skF_9','#skF_8','#skF_10')) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_88,plain,(
    r2_hidden('#skF_13',k2_relset_1('#skF_9','#skF_8','#skF_10')) ),
    inference(splitLeft,[status(thm)],[c_76])).

tff(c_1740,plain,(
    r2_hidden('#skF_13',k2_relat_1('#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1032,c_88])).

tff(c_42,plain,(
    ! [A_37,B_38] : v1_relat_1(k2_zfmisc_1(A_37,B_38)) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_80,plain,(
    ! [B_104,A_105] :
      ( v1_relat_1(B_104)
      | ~ m1_subset_1(B_104,k1_zfmisc_1(A_105))
      | ~ v1_relat_1(A_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_83,plain,
    ( v1_relat_1('#skF_10')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_9','#skF_8')) ),
    inference(resolution,[status(thm)],[c_60,c_80])).

tff(c_86,plain,(
    v1_relat_1('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_83])).

tff(c_52,plain,(
    ! [A_45] :
      ( k9_relat_1(A_45,k1_relat_1(A_45)) = k2_relat_1(A_45)
      | ~ v1_relat_1(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_50,plain,(
    ! [A_39,B_40,C_41] :
      ( r2_hidden('#skF_7'(A_39,B_40,C_41),k1_relat_1(C_41))
      | ~ r2_hidden(A_39,k9_relat_1(C_41,B_40))
      | ~ v1_relat_1(C_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1008,plain,(
    ! [A_206,B_207,C_208] :
      ( k1_relset_1(A_206,B_207,C_208) = k1_relat_1(C_208)
      | ~ m1_subset_1(C_208,k1_zfmisc_1(k2_zfmisc_1(A_206,B_207))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1017,plain,(
    k1_relset_1('#skF_9','#skF_8','#skF_10') = k1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_60,c_1008])).

tff(c_1797,plain,(
    ! [A_284,B_285,C_286] :
      ( m1_subset_1(k1_relset_1(A_284,B_285,C_286),k1_zfmisc_1(A_284))
      | ~ m1_subset_1(C_286,k1_zfmisc_1(k2_zfmisc_1(A_284,B_285))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_1819,plain,
    ( m1_subset_1(k1_relat_1('#skF_10'),k1_zfmisc_1('#skF_9'))
    | ~ m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_9','#skF_8'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1017,c_1797])).

tff(c_1827,plain,(
    m1_subset_1(k1_relat_1('#skF_10'),k1_zfmisc_1('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_1819])).

tff(c_24,plain,(
    ! [A_11,B_12] :
      ( k3_subset_1(A_11,k3_subset_1(A_11,B_12)) = B_12
      | ~ m1_subset_1(B_12,k1_zfmisc_1(A_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1841,plain,(
    k3_subset_1('#skF_9',k3_subset_1('#skF_9',k1_relat_1('#skF_10'))) = k1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_1827,c_24])).

tff(c_112,plain,(
    ! [A_117,B_118] :
      ( m1_subset_1(k3_subset_1(A_117,B_118),k1_zfmisc_1(A_117))
      | ~ m1_subset_1(B_118,k1_zfmisc_1(A_117)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_20,plain,(
    ! [A_7,B_8] :
      ( k4_xboole_0(A_7,B_8) = k3_subset_1(A_7,B_8)
      | ~ m1_subset_1(B_8,k1_zfmisc_1(A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2053,plain,(
    ! [A_307,B_308] :
      ( k4_xboole_0(A_307,k3_subset_1(A_307,B_308)) = k3_subset_1(A_307,k3_subset_1(A_307,B_308))
      | ~ m1_subset_1(B_308,k1_zfmisc_1(A_307)) ) ),
    inference(resolution,[status(thm)],[c_112,c_20])).

tff(c_2058,plain,(
    k4_xboole_0('#skF_9',k3_subset_1('#skF_9',k1_relat_1('#skF_10'))) = k3_subset_1('#skF_9',k3_subset_1('#skF_9',k1_relat_1('#skF_10'))) ),
    inference(resolution,[status(thm)],[c_1827,c_2053])).

tff(c_2067,plain,(
    k4_xboole_0('#skF_9',k3_subset_1('#skF_9',k1_relat_1('#skF_10'))) = k1_relat_1('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1841,c_2058])).

tff(c_6,plain,(
    ! [D_6,A_1,B_2] :
      ( r2_hidden(D_6,A_1)
      | ~ r2_hidden(D_6,k4_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2088,plain,(
    ! [D_309] :
      ( r2_hidden(D_309,'#skF_9')
      | ~ r2_hidden(D_309,k1_relat_1('#skF_10')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2067,c_6])).

tff(c_2092,plain,(
    ! [A_39,B_40] :
      ( r2_hidden('#skF_7'(A_39,B_40,'#skF_10'),'#skF_9')
      | ~ r2_hidden(A_39,k9_relat_1('#skF_10',B_40))
      | ~ v1_relat_1('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_50,c_2088])).

tff(c_2333,plain,(
    ! [A_329,B_330] :
      ( r2_hidden('#skF_7'(A_329,B_330,'#skF_10'),'#skF_9')
      | ~ r2_hidden(A_329,k9_relat_1('#skF_10',B_330)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_2092])).

tff(c_26,plain,(
    ! [A_13,B_14] :
      ( m1_subset_1(A_13,B_14)
      | ~ r2_hidden(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2338,plain,(
    ! [A_331,B_332] :
      ( m1_subset_1('#skF_7'(A_331,B_332,'#skF_10'),'#skF_9')
      | ~ r2_hidden(A_331,k9_relat_1('#skF_10',B_332)) ) ),
    inference(resolution,[status(thm)],[c_2333,c_26])).

tff(c_2354,plain,(
    ! [A_331] :
      ( m1_subset_1('#skF_7'(A_331,k1_relat_1('#skF_10'),'#skF_10'),'#skF_9')
      | ~ r2_hidden(A_331,k2_relat_1('#skF_10'))
      | ~ v1_relat_1('#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_2338])).

tff(c_2360,plain,(
    ! [A_333] :
      ( m1_subset_1('#skF_7'(A_333,k1_relat_1('#skF_10'),'#skF_10'),'#skF_9')
      | ~ r2_hidden(A_333,k2_relat_1('#skF_10')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_2354])).

tff(c_2106,plain,(
    ! [A_310,B_311,C_312] :
      ( r2_hidden(k4_tarski('#skF_7'(A_310,B_311,C_312),A_310),C_312)
      | ~ r2_hidden(A_310,k9_relat_1(C_312,B_311))
      | ~ v1_relat_1(C_312) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1035,plain,(
    r2_hidden('#skF_13',k2_relat_1('#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1032,c_88])).

tff(c_1120,plain,(
    ! [A_221,B_222,C_223] :
      ( m1_subset_1(k1_relset_1(A_221,B_222,C_223),k1_zfmisc_1(A_221))
      | ~ m1_subset_1(C_223,k1_zfmisc_1(k2_zfmisc_1(A_221,B_222))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_1142,plain,
    ( m1_subset_1(k1_relat_1('#skF_10'),k1_zfmisc_1('#skF_9'))
    | ~ m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_9','#skF_8'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1017,c_1120])).

tff(c_1150,plain,(
    m1_subset_1(k1_relat_1('#skF_10'),k1_zfmisc_1('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_1142])).

tff(c_1164,plain,(
    k3_subset_1('#skF_9',k3_subset_1('#skF_9',k1_relat_1('#skF_10'))) = k1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_1150,c_24])).

tff(c_1396,plain,(
    ! [A_245,B_246] :
      ( k4_xboole_0(A_245,k3_subset_1(A_245,B_246)) = k3_subset_1(A_245,k3_subset_1(A_245,B_246))
      | ~ m1_subset_1(B_246,k1_zfmisc_1(A_245)) ) ),
    inference(resolution,[status(thm)],[c_112,c_20])).

tff(c_1401,plain,(
    k4_xboole_0('#skF_9',k3_subset_1('#skF_9',k1_relat_1('#skF_10'))) = k3_subset_1('#skF_9',k3_subset_1('#skF_9',k1_relat_1('#skF_10'))) ),
    inference(resolution,[status(thm)],[c_1150,c_1396])).

tff(c_1410,plain,(
    k4_xboole_0('#skF_9',k3_subset_1('#skF_9',k1_relat_1('#skF_10'))) = k1_relat_1('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1164,c_1401])).

tff(c_1431,plain,(
    ! [D_247] :
      ( r2_hidden(D_247,'#skF_9')
      | ~ r2_hidden(D_247,k1_relat_1('#skF_10')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1410,c_6])).

tff(c_1435,plain,(
    ! [A_39,B_40] :
      ( r2_hidden('#skF_7'(A_39,B_40,'#skF_10'),'#skF_9')
      | ~ r2_hidden(A_39,k9_relat_1('#skF_10',B_40))
      | ~ v1_relat_1('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_50,c_1431])).

tff(c_1616,plain,(
    ! [A_262,B_263] :
      ( r2_hidden('#skF_7'(A_262,B_263,'#skF_10'),'#skF_9')
      | ~ r2_hidden(A_262,k9_relat_1('#skF_10',B_263)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_1435])).

tff(c_1664,plain,(
    ! [A_269,B_270] :
      ( m1_subset_1('#skF_7'(A_269,B_270,'#skF_10'),'#skF_9')
      | ~ r2_hidden(A_269,k9_relat_1('#skF_10',B_270)) ) ),
    inference(resolution,[status(thm)],[c_1616,c_26])).

tff(c_1680,plain,(
    ! [A_269] :
      ( m1_subset_1('#skF_7'(A_269,k1_relat_1('#skF_10'),'#skF_10'),'#skF_9')
      | ~ r2_hidden(A_269,k2_relat_1('#skF_10'))
      | ~ v1_relat_1('#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_1664])).

tff(c_1686,plain,(
    ! [A_271] :
      ( m1_subset_1('#skF_7'(A_271,k1_relat_1('#skF_10'),'#skF_10'),'#skF_9')
      | ~ r2_hidden(A_271,k2_relat_1('#skF_10')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_1680])).

tff(c_1480,plain,(
    ! [A_249,B_250,C_251] :
      ( r2_hidden(k4_tarski('#skF_7'(A_249,B_250,C_251),A_249),C_251)
      | ~ r2_hidden(A_249,k9_relat_1(C_251,B_250))
      | ~ v1_relat_1(C_251) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_68,plain,(
    ! [E_96] :
      ( r2_hidden(k4_tarski('#skF_12','#skF_11'),'#skF_10')
      | ~ r2_hidden(k4_tarski(E_96,'#skF_13'),'#skF_10')
      | ~ m1_subset_1(E_96,'#skF_9') ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_1033,plain,(
    ! [E_96] :
      ( ~ r2_hidden(k4_tarski(E_96,'#skF_13'),'#skF_10')
      | ~ m1_subset_1(E_96,'#skF_9') ) ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_1503,plain,(
    ! [B_250] :
      ( ~ m1_subset_1('#skF_7'('#skF_13',B_250,'#skF_10'),'#skF_9')
      | ~ r2_hidden('#skF_13',k9_relat_1('#skF_10',B_250))
      | ~ v1_relat_1('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_1480,c_1033])).

tff(c_1559,plain,(
    ! [B_256] :
      ( ~ m1_subset_1('#skF_7'('#skF_13',B_256,'#skF_10'),'#skF_9')
      | ~ r2_hidden('#skF_13',k9_relat_1('#skF_10',B_256)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_1503])).

tff(c_1563,plain,
    ( ~ m1_subset_1('#skF_7'('#skF_13',k1_relat_1('#skF_10'),'#skF_10'),'#skF_9')
    | ~ r2_hidden('#skF_13',k2_relat_1('#skF_10'))
    | ~ v1_relat_1('#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_1559])).

tff(c_1565,plain,(
    ~ m1_subset_1('#skF_7'('#skF_13',k1_relat_1('#skF_10'),'#skF_10'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_1035,c_1563])).

tff(c_1689,plain,(
    ~ r2_hidden('#skF_13',k2_relat_1('#skF_10')) ),
    inference(resolution,[status(thm)],[c_1686,c_1565])).

tff(c_1693,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1035,c_1689])).

tff(c_1694,plain,(
    r2_hidden(k4_tarski('#skF_12','#skF_11'),'#skF_10') ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_32,plain,(
    ! [C_33,A_18,D_36] :
      ( r2_hidden(C_33,k2_relat_1(A_18))
      | ~ r2_hidden(k4_tarski(D_36,C_33),A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_1702,plain,(
    r2_hidden('#skF_11',k2_relat_1('#skF_10')) ),
    inference(resolution,[status(thm)],[c_1694,c_32])).

tff(c_66,plain,(
    ! [E_96] :
      ( ~ r2_hidden('#skF_11',k2_relset_1('#skF_9','#skF_8','#skF_10'))
      | ~ r2_hidden(k4_tarski(E_96,'#skF_13'),'#skF_10')
      | ~ m1_subset_1(E_96,'#skF_9') ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_1695,plain,(
    ~ r2_hidden('#skF_11',k2_relset_1('#skF_9','#skF_8','#skF_10')) ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_1714,plain,(
    ~ r2_hidden('#skF_11',k2_relat_1('#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1032,c_1695])).

tff(c_1719,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1702,c_1714])).

tff(c_1720,plain,(
    ! [E_96] :
      ( ~ r2_hidden(k4_tarski(E_96,'#skF_13'),'#skF_10')
      | ~ m1_subset_1(E_96,'#skF_9') ) ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_2132,plain,(
    ! [B_311] :
      ( ~ m1_subset_1('#skF_7'('#skF_13',B_311,'#skF_10'),'#skF_9')
      | ~ r2_hidden('#skF_13',k9_relat_1('#skF_10',B_311))
      | ~ v1_relat_1('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_2106,c_1720])).

tff(c_2207,plain,(
    ! [B_315] :
      ( ~ m1_subset_1('#skF_7'('#skF_13',B_315,'#skF_10'),'#skF_9')
      | ~ r2_hidden('#skF_13',k9_relat_1('#skF_10',B_315)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_2132])).

tff(c_2211,plain,
    ( ~ m1_subset_1('#skF_7'('#skF_13',k1_relat_1('#skF_10'),'#skF_10'),'#skF_9')
    | ~ r2_hidden('#skF_13',k2_relat_1('#skF_10'))
    | ~ v1_relat_1('#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_2207])).

tff(c_2213,plain,(
    ~ m1_subset_1('#skF_7'('#skF_13',k1_relat_1('#skF_10'),'#skF_10'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_1740,c_2211])).

tff(c_2363,plain,(
    ~ r2_hidden('#skF_13',k2_relat_1('#skF_10')) ),
    inference(resolution,[status(thm)],[c_2360,c_2213])).

tff(c_2367,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1740,c_2363])).

tff(c_2369,plain,(
    ~ r2_hidden('#skF_13',k2_relset_1('#skF_9','#skF_8','#skF_10')) ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_74,plain,
    ( r2_hidden(k4_tarski('#skF_12','#skF_11'),'#skF_10')
    | r2_hidden('#skF_13',k2_relset_1('#skF_9','#skF_8','#skF_10')) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_2431,plain,(
    r2_hidden(k4_tarski('#skF_12','#skF_11'),'#skF_10') ),
    inference(negUnitSimplification,[status(thm)],[c_2369,c_74])).

tff(c_2438,plain,(
    r2_hidden('#skF_11',k2_relat_1('#skF_10')) ),
    inference(resolution,[status(thm)],[c_2431,c_32])).

tff(c_2485,plain,(
    ! [A_356,B_357,C_358] :
      ( k2_relset_1(A_356,B_357,C_358) = k2_relat_1(C_358)
      | ~ m1_subset_1(C_358,k1_zfmisc_1(k2_zfmisc_1(A_356,B_357))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_2494,plain,(
    k2_relset_1('#skF_9','#skF_8','#skF_10') = k2_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_60,c_2485])).

tff(c_72,plain,
    ( ~ r2_hidden('#skF_11',k2_relset_1('#skF_9','#skF_8','#skF_10'))
    | r2_hidden('#skF_13',k2_relset_1('#skF_9','#skF_8','#skF_10')) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_2444,plain,(
    ~ r2_hidden('#skF_11',k2_relset_1('#skF_9','#skF_8','#skF_10')) ),
    inference(negUnitSimplification,[status(thm)],[c_2369,c_72])).

tff(c_2495,plain,(
    ~ r2_hidden('#skF_11',k2_relat_1('#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2494,c_2444])).

tff(c_2499,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2438,c_2495])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n012.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 14:59:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.05/1.77  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.49/1.79  
% 4.49/1.79  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.49/1.79  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k4_xboole_0 > k4_tarski > k3_subset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_11 > #skF_6 > #skF_3 > #skF_10 > #skF_13 > #skF_2 > #skF_9 > #skF_7 > #skF_8 > #skF_5 > #skF_12 > #skF_4
% 4.49/1.79  
% 4.49/1.79  %Foreground sorts:
% 4.49/1.79  
% 4.49/1.79  
% 4.49/1.79  %Background operators:
% 4.49/1.79  
% 4.49/1.79  
% 4.49/1.79  %Foreground operators:
% 4.49/1.79  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.49/1.79  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.49/1.79  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.49/1.79  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.49/1.79  tff('#skF_11', type, '#skF_11': $i).
% 4.49/1.79  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 4.49/1.79  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.49/1.79  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 4.49/1.79  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.49/1.79  tff('#skF_10', type, '#skF_10': $i).
% 4.49/1.79  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.49/1.79  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 4.49/1.79  tff('#skF_13', type, '#skF_13': $i).
% 4.49/1.79  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 4.49/1.79  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.49/1.79  tff('#skF_9', type, '#skF_9': $i).
% 4.49/1.79  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.49/1.79  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.49/1.79  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 4.49/1.79  tff('#skF_8', type, '#skF_8': $i).
% 4.49/1.79  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.49/1.79  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.49/1.79  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.49/1.79  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.49/1.79  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.49/1.79  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 4.49/1.79  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.49/1.79  tff('#skF_12', type, '#skF_12': $i).
% 4.49/1.79  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 4.49/1.79  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.49/1.79  
% 4.65/1.82  tff(f_114, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => (![D]: (r2_hidden(D, k2_relset_1(B, A, C)) <=> (?[E]: (m1_subset_1(E, B) & r2_hidden(k4_tarski(E, D), C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_relset_1)).
% 4.65/1.82  tff(f_95, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.65/1.82  tff(f_68, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 4.65/1.82  tff(f_58, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 4.65/1.82  tff(f_83, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 4.65/1.82  tff(f_79, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_relat_1)).
% 4.65/1.82  tff(f_91, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.65/1.82  tff(f_87, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k1_relset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 4.65/1.82  tff(f_47, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 4.65/1.82  tff(f_43, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 4.65/1.82  tff(f_39, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 4.65/1.82  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 4.65/1.82  tff(f_51, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 4.65/1.82  tff(f_66, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_relat_1)).
% 4.65/1.82  tff(c_60, plain, (m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1('#skF_9', '#skF_8')))), inference(cnfTransformation, [status(thm)], [f_114])).
% 4.65/1.82  tff(c_1023, plain, (![A_209, B_210, C_211]: (k2_relset_1(A_209, B_210, C_211)=k2_relat_1(C_211) | ~m1_subset_1(C_211, k1_zfmisc_1(k2_zfmisc_1(A_209, B_210))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.65/1.82  tff(c_1032, plain, (k2_relset_1('#skF_9', '#skF_8', '#skF_10')=k2_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_60, c_1023])).
% 4.65/1.82  tff(c_76, plain, (m1_subset_1('#skF_12', '#skF_9') | r2_hidden('#skF_13', k2_relset_1('#skF_9', '#skF_8', '#skF_10'))), inference(cnfTransformation, [status(thm)], [f_114])).
% 4.65/1.82  tff(c_88, plain, (r2_hidden('#skF_13', k2_relset_1('#skF_9', '#skF_8', '#skF_10'))), inference(splitLeft, [status(thm)], [c_76])).
% 4.65/1.82  tff(c_1740, plain, (r2_hidden('#skF_13', k2_relat_1('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_1032, c_88])).
% 4.65/1.82  tff(c_42, plain, (![A_37, B_38]: (v1_relat_1(k2_zfmisc_1(A_37, B_38)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.65/1.82  tff(c_80, plain, (![B_104, A_105]: (v1_relat_1(B_104) | ~m1_subset_1(B_104, k1_zfmisc_1(A_105)) | ~v1_relat_1(A_105))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.65/1.82  tff(c_83, plain, (v1_relat_1('#skF_10') | ~v1_relat_1(k2_zfmisc_1('#skF_9', '#skF_8'))), inference(resolution, [status(thm)], [c_60, c_80])).
% 4.65/1.82  tff(c_86, plain, (v1_relat_1('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_83])).
% 4.65/1.82  tff(c_52, plain, (![A_45]: (k9_relat_1(A_45, k1_relat_1(A_45))=k2_relat_1(A_45) | ~v1_relat_1(A_45))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.65/1.82  tff(c_50, plain, (![A_39, B_40, C_41]: (r2_hidden('#skF_7'(A_39, B_40, C_41), k1_relat_1(C_41)) | ~r2_hidden(A_39, k9_relat_1(C_41, B_40)) | ~v1_relat_1(C_41))), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.65/1.82  tff(c_1008, plain, (![A_206, B_207, C_208]: (k1_relset_1(A_206, B_207, C_208)=k1_relat_1(C_208) | ~m1_subset_1(C_208, k1_zfmisc_1(k2_zfmisc_1(A_206, B_207))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.65/1.82  tff(c_1017, plain, (k1_relset_1('#skF_9', '#skF_8', '#skF_10')=k1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_60, c_1008])).
% 4.65/1.82  tff(c_1797, plain, (![A_284, B_285, C_286]: (m1_subset_1(k1_relset_1(A_284, B_285, C_286), k1_zfmisc_1(A_284)) | ~m1_subset_1(C_286, k1_zfmisc_1(k2_zfmisc_1(A_284, B_285))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.65/1.82  tff(c_1819, plain, (m1_subset_1(k1_relat_1('#skF_10'), k1_zfmisc_1('#skF_9')) | ~m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1('#skF_9', '#skF_8')))), inference(superposition, [status(thm), theory('equality')], [c_1017, c_1797])).
% 4.65/1.82  tff(c_1827, plain, (m1_subset_1(k1_relat_1('#skF_10'), k1_zfmisc_1('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_1819])).
% 4.65/1.82  tff(c_24, plain, (![A_11, B_12]: (k3_subset_1(A_11, k3_subset_1(A_11, B_12))=B_12 | ~m1_subset_1(B_12, k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.65/1.82  tff(c_1841, plain, (k3_subset_1('#skF_9', k3_subset_1('#skF_9', k1_relat_1('#skF_10')))=k1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_1827, c_24])).
% 4.65/1.82  tff(c_112, plain, (![A_117, B_118]: (m1_subset_1(k3_subset_1(A_117, B_118), k1_zfmisc_1(A_117)) | ~m1_subset_1(B_118, k1_zfmisc_1(A_117)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.65/1.82  tff(c_20, plain, (![A_7, B_8]: (k4_xboole_0(A_7, B_8)=k3_subset_1(A_7, B_8) | ~m1_subset_1(B_8, k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.65/1.82  tff(c_2053, plain, (![A_307, B_308]: (k4_xboole_0(A_307, k3_subset_1(A_307, B_308))=k3_subset_1(A_307, k3_subset_1(A_307, B_308)) | ~m1_subset_1(B_308, k1_zfmisc_1(A_307)))), inference(resolution, [status(thm)], [c_112, c_20])).
% 4.65/1.82  tff(c_2058, plain, (k4_xboole_0('#skF_9', k3_subset_1('#skF_9', k1_relat_1('#skF_10')))=k3_subset_1('#skF_9', k3_subset_1('#skF_9', k1_relat_1('#skF_10')))), inference(resolution, [status(thm)], [c_1827, c_2053])).
% 4.65/1.82  tff(c_2067, plain, (k4_xboole_0('#skF_9', k3_subset_1('#skF_9', k1_relat_1('#skF_10')))=k1_relat_1('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_1841, c_2058])).
% 4.65/1.82  tff(c_6, plain, (![D_6, A_1, B_2]: (r2_hidden(D_6, A_1) | ~r2_hidden(D_6, k4_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.65/1.82  tff(c_2088, plain, (![D_309]: (r2_hidden(D_309, '#skF_9') | ~r2_hidden(D_309, k1_relat_1('#skF_10')))), inference(superposition, [status(thm), theory('equality')], [c_2067, c_6])).
% 4.65/1.82  tff(c_2092, plain, (![A_39, B_40]: (r2_hidden('#skF_7'(A_39, B_40, '#skF_10'), '#skF_9') | ~r2_hidden(A_39, k9_relat_1('#skF_10', B_40)) | ~v1_relat_1('#skF_10'))), inference(resolution, [status(thm)], [c_50, c_2088])).
% 4.65/1.82  tff(c_2333, plain, (![A_329, B_330]: (r2_hidden('#skF_7'(A_329, B_330, '#skF_10'), '#skF_9') | ~r2_hidden(A_329, k9_relat_1('#skF_10', B_330)))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_2092])).
% 4.65/1.82  tff(c_26, plain, (![A_13, B_14]: (m1_subset_1(A_13, B_14) | ~r2_hidden(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.65/1.82  tff(c_2338, plain, (![A_331, B_332]: (m1_subset_1('#skF_7'(A_331, B_332, '#skF_10'), '#skF_9') | ~r2_hidden(A_331, k9_relat_1('#skF_10', B_332)))), inference(resolution, [status(thm)], [c_2333, c_26])).
% 4.65/1.82  tff(c_2354, plain, (![A_331]: (m1_subset_1('#skF_7'(A_331, k1_relat_1('#skF_10'), '#skF_10'), '#skF_9') | ~r2_hidden(A_331, k2_relat_1('#skF_10')) | ~v1_relat_1('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_52, c_2338])).
% 4.65/1.82  tff(c_2360, plain, (![A_333]: (m1_subset_1('#skF_7'(A_333, k1_relat_1('#skF_10'), '#skF_10'), '#skF_9') | ~r2_hidden(A_333, k2_relat_1('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_2354])).
% 4.65/1.82  tff(c_2106, plain, (![A_310, B_311, C_312]: (r2_hidden(k4_tarski('#skF_7'(A_310, B_311, C_312), A_310), C_312) | ~r2_hidden(A_310, k9_relat_1(C_312, B_311)) | ~v1_relat_1(C_312))), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.65/1.82  tff(c_1035, plain, (r2_hidden('#skF_13', k2_relat_1('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_1032, c_88])).
% 4.65/1.82  tff(c_1120, plain, (![A_221, B_222, C_223]: (m1_subset_1(k1_relset_1(A_221, B_222, C_223), k1_zfmisc_1(A_221)) | ~m1_subset_1(C_223, k1_zfmisc_1(k2_zfmisc_1(A_221, B_222))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.65/1.82  tff(c_1142, plain, (m1_subset_1(k1_relat_1('#skF_10'), k1_zfmisc_1('#skF_9')) | ~m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1('#skF_9', '#skF_8')))), inference(superposition, [status(thm), theory('equality')], [c_1017, c_1120])).
% 4.65/1.82  tff(c_1150, plain, (m1_subset_1(k1_relat_1('#skF_10'), k1_zfmisc_1('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_1142])).
% 4.65/1.82  tff(c_1164, plain, (k3_subset_1('#skF_9', k3_subset_1('#skF_9', k1_relat_1('#skF_10')))=k1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_1150, c_24])).
% 4.65/1.82  tff(c_1396, plain, (![A_245, B_246]: (k4_xboole_0(A_245, k3_subset_1(A_245, B_246))=k3_subset_1(A_245, k3_subset_1(A_245, B_246)) | ~m1_subset_1(B_246, k1_zfmisc_1(A_245)))), inference(resolution, [status(thm)], [c_112, c_20])).
% 4.65/1.82  tff(c_1401, plain, (k4_xboole_0('#skF_9', k3_subset_1('#skF_9', k1_relat_1('#skF_10')))=k3_subset_1('#skF_9', k3_subset_1('#skF_9', k1_relat_1('#skF_10')))), inference(resolution, [status(thm)], [c_1150, c_1396])).
% 4.65/1.82  tff(c_1410, plain, (k4_xboole_0('#skF_9', k3_subset_1('#skF_9', k1_relat_1('#skF_10')))=k1_relat_1('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_1164, c_1401])).
% 4.65/1.82  tff(c_1431, plain, (![D_247]: (r2_hidden(D_247, '#skF_9') | ~r2_hidden(D_247, k1_relat_1('#skF_10')))), inference(superposition, [status(thm), theory('equality')], [c_1410, c_6])).
% 4.65/1.82  tff(c_1435, plain, (![A_39, B_40]: (r2_hidden('#skF_7'(A_39, B_40, '#skF_10'), '#skF_9') | ~r2_hidden(A_39, k9_relat_1('#skF_10', B_40)) | ~v1_relat_1('#skF_10'))), inference(resolution, [status(thm)], [c_50, c_1431])).
% 4.65/1.82  tff(c_1616, plain, (![A_262, B_263]: (r2_hidden('#skF_7'(A_262, B_263, '#skF_10'), '#skF_9') | ~r2_hidden(A_262, k9_relat_1('#skF_10', B_263)))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_1435])).
% 4.65/1.82  tff(c_1664, plain, (![A_269, B_270]: (m1_subset_1('#skF_7'(A_269, B_270, '#skF_10'), '#skF_9') | ~r2_hidden(A_269, k9_relat_1('#skF_10', B_270)))), inference(resolution, [status(thm)], [c_1616, c_26])).
% 4.65/1.82  tff(c_1680, plain, (![A_269]: (m1_subset_1('#skF_7'(A_269, k1_relat_1('#skF_10'), '#skF_10'), '#skF_9') | ~r2_hidden(A_269, k2_relat_1('#skF_10')) | ~v1_relat_1('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_52, c_1664])).
% 4.65/1.82  tff(c_1686, plain, (![A_271]: (m1_subset_1('#skF_7'(A_271, k1_relat_1('#skF_10'), '#skF_10'), '#skF_9') | ~r2_hidden(A_271, k2_relat_1('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_1680])).
% 4.65/1.82  tff(c_1480, plain, (![A_249, B_250, C_251]: (r2_hidden(k4_tarski('#skF_7'(A_249, B_250, C_251), A_249), C_251) | ~r2_hidden(A_249, k9_relat_1(C_251, B_250)) | ~v1_relat_1(C_251))), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.65/1.82  tff(c_68, plain, (![E_96]: (r2_hidden(k4_tarski('#skF_12', '#skF_11'), '#skF_10') | ~r2_hidden(k4_tarski(E_96, '#skF_13'), '#skF_10') | ~m1_subset_1(E_96, '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_114])).
% 4.65/1.82  tff(c_1033, plain, (![E_96]: (~r2_hidden(k4_tarski(E_96, '#skF_13'), '#skF_10') | ~m1_subset_1(E_96, '#skF_9'))), inference(splitLeft, [status(thm)], [c_68])).
% 4.65/1.82  tff(c_1503, plain, (![B_250]: (~m1_subset_1('#skF_7'('#skF_13', B_250, '#skF_10'), '#skF_9') | ~r2_hidden('#skF_13', k9_relat_1('#skF_10', B_250)) | ~v1_relat_1('#skF_10'))), inference(resolution, [status(thm)], [c_1480, c_1033])).
% 4.65/1.82  tff(c_1559, plain, (![B_256]: (~m1_subset_1('#skF_7'('#skF_13', B_256, '#skF_10'), '#skF_9') | ~r2_hidden('#skF_13', k9_relat_1('#skF_10', B_256)))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_1503])).
% 4.65/1.82  tff(c_1563, plain, (~m1_subset_1('#skF_7'('#skF_13', k1_relat_1('#skF_10'), '#skF_10'), '#skF_9') | ~r2_hidden('#skF_13', k2_relat_1('#skF_10')) | ~v1_relat_1('#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_52, c_1559])).
% 4.65/1.82  tff(c_1565, plain, (~m1_subset_1('#skF_7'('#skF_13', k1_relat_1('#skF_10'), '#skF_10'), '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_1035, c_1563])).
% 4.65/1.82  tff(c_1689, plain, (~r2_hidden('#skF_13', k2_relat_1('#skF_10'))), inference(resolution, [status(thm)], [c_1686, c_1565])).
% 4.65/1.82  tff(c_1693, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1035, c_1689])).
% 4.65/1.82  tff(c_1694, plain, (r2_hidden(k4_tarski('#skF_12', '#skF_11'), '#skF_10')), inference(splitRight, [status(thm)], [c_68])).
% 4.65/1.82  tff(c_32, plain, (![C_33, A_18, D_36]: (r2_hidden(C_33, k2_relat_1(A_18)) | ~r2_hidden(k4_tarski(D_36, C_33), A_18))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.65/1.82  tff(c_1702, plain, (r2_hidden('#skF_11', k2_relat_1('#skF_10'))), inference(resolution, [status(thm)], [c_1694, c_32])).
% 4.65/1.82  tff(c_66, plain, (![E_96]: (~r2_hidden('#skF_11', k2_relset_1('#skF_9', '#skF_8', '#skF_10')) | ~r2_hidden(k4_tarski(E_96, '#skF_13'), '#skF_10') | ~m1_subset_1(E_96, '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_114])).
% 4.65/1.82  tff(c_1695, plain, (~r2_hidden('#skF_11', k2_relset_1('#skF_9', '#skF_8', '#skF_10'))), inference(splitLeft, [status(thm)], [c_66])).
% 4.65/1.82  tff(c_1714, plain, (~r2_hidden('#skF_11', k2_relat_1('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_1032, c_1695])).
% 4.65/1.82  tff(c_1719, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1702, c_1714])).
% 4.65/1.82  tff(c_1720, plain, (![E_96]: (~r2_hidden(k4_tarski(E_96, '#skF_13'), '#skF_10') | ~m1_subset_1(E_96, '#skF_9'))), inference(splitRight, [status(thm)], [c_66])).
% 4.65/1.82  tff(c_2132, plain, (![B_311]: (~m1_subset_1('#skF_7'('#skF_13', B_311, '#skF_10'), '#skF_9') | ~r2_hidden('#skF_13', k9_relat_1('#skF_10', B_311)) | ~v1_relat_1('#skF_10'))), inference(resolution, [status(thm)], [c_2106, c_1720])).
% 4.65/1.82  tff(c_2207, plain, (![B_315]: (~m1_subset_1('#skF_7'('#skF_13', B_315, '#skF_10'), '#skF_9') | ~r2_hidden('#skF_13', k9_relat_1('#skF_10', B_315)))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_2132])).
% 4.65/1.82  tff(c_2211, plain, (~m1_subset_1('#skF_7'('#skF_13', k1_relat_1('#skF_10'), '#skF_10'), '#skF_9') | ~r2_hidden('#skF_13', k2_relat_1('#skF_10')) | ~v1_relat_1('#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_52, c_2207])).
% 4.65/1.82  tff(c_2213, plain, (~m1_subset_1('#skF_7'('#skF_13', k1_relat_1('#skF_10'), '#skF_10'), '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_1740, c_2211])).
% 4.65/1.82  tff(c_2363, plain, (~r2_hidden('#skF_13', k2_relat_1('#skF_10'))), inference(resolution, [status(thm)], [c_2360, c_2213])).
% 4.65/1.82  tff(c_2367, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1740, c_2363])).
% 4.65/1.82  tff(c_2369, plain, (~r2_hidden('#skF_13', k2_relset_1('#skF_9', '#skF_8', '#skF_10'))), inference(splitRight, [status(thm)], [c_76])).
% 4.65/1.82  tff(c_74, plain, (r2_hidden(k4_tarski('#skF_12', '#skF_11'), '#skF_10') | r2_hidden('#skF_13', k2_relset_1('#skF_9', '#skF_8', '#skF_10'))), inference(cnfTransformation, [status(thm)], [f_114])).
% 4.65/1.82  tff(c_2431, plain, (r2_hidden(k4_tarski('#skF_12', '#skF_11'), '#skF_10')), inference(negUnitSimplification, [status(thm)], [c_2369, c_74])).
% 4.65/1.82  tff(c_2438, plain, (r2_hidden('#skF_11', k2_relat_1('#skF_10'))), inference(resolution, [status(thm)], [c_2431, c_32])).
% 4.65/1.82  tff(c_2485, plain, (![A_356, B_357, C_358]: (k2_relset_1(A_356, B_357, C_358)=k2_relat_1(C_358) | ~m1_subset_1(C_358, k1_zfmisc_1(k2_zfmisc_1(A_356, B_357))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.65/1.82  tff(c_2494, plain, (k2_relset_1('#skF_9', '#skF_8', '#skF_10')=k2_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_60, c_2485])).
% 4.65/1.82  tff(c_72, plain, (~r2_hidden('#skF_11', k2_relset_1('#skF_9', '#skF_8', '#skF_10')) | r2_hidden('#skF_13', k2_relset_1('#skF_9', '#skF_8', '#skF_10'))), inference(cnfTransformation, [status(thm)], [f_114])).
% 4.65/1.82  tff(c_2444, plain, (~r2_hidden('#skF_11', k2_relset_1('#skF_9', '#skF_8', '#skF_10'))), inference(negUnitSimplification, [status(thm)], [c_2369, c_72])).
% 4.65/1.82  tff(c_2495, plain, (~r2_hidden('#skF_11', k2_relat_1('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_2494, c_2444])).
% 4.65/1.82  tff(c_2499, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2438, c_2495])).
% 4.65/1.82  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.65/1.82  
% 4.65/1.82  Inference rules
% 4.65/1.82  ----------------------
% 4.65/1.82  #Ref     : 0
% 4.65/1.82  #Sup     : 535
% 4.65/1.82  #Fact    : 0
% 4.65/1.82  #Define  : 0
% 4.65/1.82  #Split   : 7
% 4.65/1.82  #Chain   : 0
% 4.65/1.82  #Close   : 0
% 4.65/1.82  
% 4.65/1.82  Ordering : KBO
% 4.65/1.82  
% 4.65/1.82  Simplification rules
% 4.65/1.82  ----------------------
% 4.65/1.82  #Subsume      : 44
% 4.65/1.82  #Demod        : 110
% 4.65/1.82  #Tautology    : 116
% 4.65/1.82  #SimpNegUnit  : 2
% 4.65/1.82  #BackRed      : 12
% 4.65/1.82  
% 4.65/1.82  #Partial instantiations: 0
% 4.65/1.82  #Strategies tried      : 1
% 4.65/1.82  
% 4.65/1.82  Timing (in seconds)
% 4.65/1.82  ----------------------
% 4.65/1.82  Preprocessing        : 0.35
% 4.65/1.82  Parsing              : 0.17
% 4.65/1.82  CNF conversion       : 0.03
% 4.65/1.82  Main loop            : 0.69
% 4.65/1.82  Inferencing          : 0.25
% 4.65/1.82  Reduction            : 0.21
% 4.65/1.82  Demodulation         : 0.15
% 4.65/1.82  BG Simplification    : 0.04
% 4.65/1.83  Subsumption          : 0.12
% 4.65/1.83  Abstraction          : 0.04
% 4.65/1.83  MUC search           : 0.00
% 4.65/1.83  Cooper               : 0.00
% 4.65/1.83  Total                : 1.09
% 4.65/1.83  Index Insertion      : 0.00
% 4.65/1.83  Index Deletion       : 0.00
% 4.65/1.83  Index Matching       : 0.00
% 4.65/1.83  BG Taut test         : 0.00
%------------------------------------------------------------------------------
