%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0680+1.003 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:41 EST 2020

% Result     : Theorem 10.81s
% Output     : CNFRefutation 10.81s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 495 expanded)
%              Number of leaves         :   25 ( 195 expanded)
%              Depth                    :   21
%              Number of atoms          :  168 (1310 expanded)
%              Number of equality atoms :   63 ( 419 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k6_subset_1 > k4_xboole_0 > k1_funct_1 > k11_relat_1 > #nlpp > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_71,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( ! [B,C] : k9_relat_1(A,k6_subset_1(B,C)) = k6_subset_1(k9_relat_1(A,B),k9_relat_1(A,C))
         => v2_funct_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t124_funct_1)).

tff(f_61,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_46,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k11_relat_1(A,B) = k9_relat_1(A,k1_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).

tff(f_44,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
      <=> ! [B,C] :
            ( ( r2_hidden(B,k1_relat_1(A))
              & r2_hidden(C,k1_relat_1(A))
              & k1_funct_1(A,B) = k1_funct_1(A,C) )
           => B = C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_funct_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => k11_relat_1(B,A) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_funct_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(c_24,plain,(
    ~ v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_30,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_28,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_22,plain,(
    ! [A_17] : k4_xboole_0(A_17,k1_xboole_0) = A_17 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_14,plain,(
    ! [A_11,B_12] : k6_subset_1(A_11,B_12) = k4_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_2,plain,(
    ! [A_1,B_3] :
      ( k9_relat_1(A_1,k1_tarski(B_3)) = k11_relat_1(A_1,B_3)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_26,plain,(
    ! [B_20,C_21] : k6_subset_1(k9_relat_1('#skF_3',B_20),k9_relat_1('#skF_3',C_21)) = k9_relat_1('#skF_3',k6_subset_1(B_20,C_21)) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_83,plain,(
    ! [B_31,C_32] : k6_subset_1(k9_relat_1('#skF_3',B_31),k9_relat_1('#skF_3',C_32)) = k9_relat_1('#skF_3',k4_xboole_0(B_31,C_32)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_26])).

tff(c_96,plain,(
    ! [B_3,C_32] :
      ( k9_relat_1('#skF_3',k4_xboole_0(k1_tarski(B_3),C_32)) = k6_subset_1(k11_relat_1('#skF_3',B_3),k9_relat_1('#skF_3',C_32))
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_83])).

tff(c_143,plain,(
    ! [B_38,C_39] : k9_relat_1('#skF_3',k4_xboole_0(k1_tarski(B_38),C_39)) = k4_xboole_0(k11_relat_1('#skF_3',B_38),k9_relat_1('#skF_3',C_39)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_14,c_96])).

tff(c_168,plain,(
    ! [B_38] : k4_xboole_0(k11_relat_1('#skF_3',B_38),k9_relat_1('#skF_3',k1_xboole_0)) = k9_relat_1('#skF_3',k1_tarski(B_38)) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_143])).

tff(c_12,plain,(
    ! [A_4] :
      ( r2_hidden('#skF_1'(A_4),k1_relat_1(A_4))
      | v2_funct_1(A_4)
      | ~ v1_funct_1(A_4)
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_303,plain,(
    ! [B_52,A_53] :
      ( k1_tarski(k1_funct_1(B_52,A_53)) = k11_relat_1(B_52,A_53)
      | ~ r2_hidden(A_53,k1_relat_1(B_52))
      | ~ v1_funct_1(B_52)
      | ~ v1_relat_1(B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_311,plain,(
    ! [A_4] :
      ( k1_tarski(k1_funct_1(A_4,'#skF_1'(A_4))) = k11_relat_1(A_4,'#skF_1'(A_4))
      | v2_funct_1(A_4)
      | ~ v1_funct_1(A_4)
      | ~ v1_relat_1(A_4) ) ),
    inference(resolution,[status(thm)],[c_12,c_303])).

tff(c_8,plain,(
    ! [A_4] :
      ( k1_funct_1(A_4,'#skF_2'(A_4)) = k1_funct_1(A_4,'#skF_1'(A_4))
      | v2_funct_1(A_4)
      | ~ v1_funct_1(A_4)
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_10,plain,(
    ! [A_4] :
      ( r2_hidden('#skF_2'(A_4),k1_relat_1(A_4))
      | v2_funct_1(A_4)
      | ~ v1_funct_1(A_4)
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_312,plain,(
    ! [A_54] :
      ( k1_tarski(k1_funct_1(A_54,'#skF_2'(A_54))) = k11_relat_1(A_54,'#skF_2'(A_54))
      | v2_funct_1(A_54)
      | ~ v1_funct_1(A_54)
      | ~ v1_relat_1(A_54) ) ),
    inference(resolution,[status(thm)],[c_10,c_303])).

tff(c_1556,plain,(
    ! [A_116] :
      ( k1_tarski(k1_funct_1(A_116,'#skF_1'(A_116))) = k11_relat_1(A_116,'#skF_2'(A_116))
      | v2_funct_1(A_116)
      | ~ v1_funct_1(A_116)
      | ~ v1_relat_1(A_116)
      | v2_funct_1(A_116)
      | ~ v1_funct_1(A_116)
      | ~ v1_relat_1(A_116) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_312])).

tff(c_10237,plain,(
    ! [A_267] :
      ( k11_relat_1(A_267,'#skF_2'(A_267)) = k11_relat_1(A_267,'#skF_1'(A_267))
      | v2_funct_1(A_267)
      | ~ v1_funct_1(A_267)
      | ~ v1_relat_1(A_267)
      | v2_funct_1(A_267)
      | ~ v1_funct_1(A_267)
      | ~ v1_relat_1(A_267)
      | v2_funct_1(A_267)
      | ~ v1_funct_1(A_267)
      | ~ v1_relat_1(A_267) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_311,c_1556])).

tff(c_10483,plain,
    ( k4_xboole_0(k11_relat_1('#skF_3','#skF_1'('#skF_3')),k9_relat_1('#skF_3',k1_xboole_0)) = k9_relat_1('#skF_3',k1_tarski('#skF_2'('#skF_3')))
    | v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_10237,c_168])).

tff(c_10649,plain,
    ( k9_relat_1('#skF_3',k1_tarski('#skF_2'('#skF_3'))) = k9_relat_1('#skF_3',k1_tarski('#skF_1'('#skF_3')))
    | v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_30,c_28,c_30,c_28,c_168,c_10483])).

tff(c_10650,plain,(
    k9_relat_1('#skF_3',k1_tarski('#skF_2'('#skF_3'))) = k9_relat_1('#skF_3',k1_tarski('#skF_1'('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_10649])).

tff(c_10823,plain,
    ( k9_relat_1('#skF_3',k1_tarski('#skF_1'('#skF_3'))) = k11_relat_1('#skF_3','#skF_2'('#skF_3'))
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_10650,c_2])).

tff(c_10886,plain,(
    k9_relat_1('#skF_3',k1_tarski('#skF_1'('#skF_3'))) = k11_relat_1('#skF_3','#skF_2'('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_10823])).

tff(c_11135,plain,
    ( k11_relat_1('#skF_3','#skF_2'('#skF_3')) = k11_relat_1('#skF_3','#skF_1'('#skF_3'))
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_10886,c_2])).

tff(c_11189,plain,(
    k11_relat_1('#skF_3','#skF_2'('#skF_3')) = k11_relat_1('#skF_3','#skF_1'('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_11135])).

tff(c_310,plain,(
    ! [A_4] :
      ( k1_tarski(k1_funct_1(A_4,'#skF_2'(A_4))) = k11_relat_1(A_4,'#skF_2'(A_4))
      | v2_funct_1(A_4)
      | ~ v1_funct_1(A_4)
      | ~ v1_relat_1(A_4) ) ),
    inference(resolution,[status(thm)],[c_10,c_303])).

tff(c_76,plain,(
    ! [A_30] :
      ( '#skF_2'(A_30) != '#skF_1'(A_30)
      | v2_funct_1(A_30)
      | ~ v1_funct_1(A_30)
      | ~ v1_relat_1(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_79,plain,
    ( '#skF_2'('#skF_3') != '#skF_1'('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_24])).

tff(c_82,plain,(
    '#skF_2'('#skF_3') != '#skF_1'('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_79])).

tff(c_10827,plain,
    ( k9_relat_1('#skF_3',k1_tarski('#skF_1'('#skF_3'))) = k11_relat_1('#skF_3','#skF_2'('#skF_3'))
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_10650])).

tff(c_10889,plain,(
    k9_relat_1('#skF_3',k1_tarski('#skF_1'('#skF_3'))) = k11_relat_1('#skF_3','#skF_2'('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_10827])).

tff(c_11479,plain,(
    k9_relat_1('#skF_3',k1_tarski('#skF_1'('#skF_3'))) = k11_relat_1('#skF_3','#skF_1'('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11189,c_10889])).

tff(c_20,plain,(
    ! [A_15,B_16] :
      ( k4_xboole_0(k1_tarski(A_15),k1_tarski(B_16)) = k1_tarski(A_15)
      | B_16 = A_15 ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_258,plain,(
    ! [A_46,B_47] :
      ( k4_xboole_0(k11_relat_1('#skF_3',A_46),k9_relat_1('#skF_3',k1_tarski(B_47))) = k9_relat_1('#skF_3',k1_tarski(A_46))
      | B_47 = A_46 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_143])).

tff(c_271,plain,(
    ! [A_46,B_3] :
      ( k4_xboole_0(k11_relat_1('#skF_3',A_46),k11_relat_1('#skF_3',B_3)) = k9_relat_1('#skF_3',k1_tarski(A_46))
      | B_3 = A_46
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_258])).

tff(c_276,plain,(
    ! [A_46,B_3] :
      ( k4_xboole_0(k11_relat_1('#skF_3',A_46),k11_relat_1('#skF_3',B_3)) = k9_relat_1('#skF_3',k1_tarski(A_46))
      | B_3 = A_46 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_271])).

tff(c_10475,plain,(
    ! [A_46] :
      ( k4_xboole_0(k11_relat_1('#skF_3',A_46),k11_relat_1('#skF_3','#skF_1'('#skF_3'))) = k9_relat_1('#skF_3',k1_tarski(A_46))
      | A_46 = '#skF_2'('#skF_3')
      | v2_funct_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3')
      | v2_funct_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3')
      | v2_funct_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10237,c_276])).

tff(c_10643,plain,(
    ! [A_46] :
      ( k4_xboole_0(k11_relat_1('#skF_3',A_46),k11_relat_1('#skF_3','#skF_1'('#skF_3'))) = k9_relat_1('#skF_3',k1_tarski(A_46))
      | A_46 = '#skF_2'('#skF_3')
      | v2_funct_1('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_30,c_28,c_30,c_28,c_10475])).

tff(c_10644,plain,(
    ! [A_46] :
      ( k4_xboole_0(k11_relat_1('#skF_3',A_46),k11_relat_1('#skF_3','#skF_1'('#skF_3'))) = k9_relat_1('#skF_3',k1_tarski(A_46))
      | A_46 = '#skF_2'('#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_10643])).

tff(c_18,plain,(
    ! [B_16] : k4_xboole_0(k1_tarski(B_16),k1_tarski(B_16)) != k1_tarski(B_16) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1765,plain,(
    ! [A_124] :
      ( k4_xboole_0(k1_tarski(k1_funct_1(A_124,'#skF_2'(A_124))),k11_relat_1(A_124,'#skF_2'(A_124))) != k1_tarski(k1_funct_1(A_124,'#skF_2'(A_124)))
      | v2_funct_1(A_124)
      | ~ v1_funct_1(A_124)
      | ~ v1_relat_1(A_124) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_312,c_18])).

tff(c_11933,plain,(
    ! [A_269] :
      ( k4_xboole_0(k11_relat_1(A_269,'#skF_2'(A_269)),k11_relat_1(A_269,'#skF_2'(A_269))) != k1_tarski(k1_funct_1(A_269,'#skF_2'(A_269)))
      | v2_funct_1(A_269)
      | ~ v1_funct_1(A_269)
      | ~ v1_relat_1(A_269)
      | v2_funct_1(A_269)
      | ~ v1_funct_1(A_269)
      | ~ v1_relat_1(A_269) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_310,c_1765])).

tff(c_11936,plain,
    ( k4_xboole_0(k11_relat_1('#skF_3','#skF_1'('#skF_3')),k11_relat_1('#skF_3','#skF_2'('#skF_3'))) != k1_tarski(k1_funct_1('#skF_3','#skF_2'('#skF_3')))
    | v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_11189,c_11933])).

tff(c_11951,plain,
    ( k4_xboole_0(k11_relat_1('#skF_3','#skF_1'('#skF_3')),k11_relat_1('#skF_3','#skF_1'('#skF_3'))) != k1_tarski(k1_funct_1('#skF_3','#skF_2'('#skF_3')))
    | v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_30,c_28,c_11189,c_11936])).

tff(c_11952,plain,(
    k4_xboole_0(k11_relat_1('#skF_3','#skF_1'('#skF_3')),k11_relat_1('#skF_3','#skF_1'('#skF_3'))) != k1_tarski(k1_funct_1('#skF_3','#skF_2'('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_11951])).

tff(c_13386,plain,
    ( k9_relat_1('#skF_3',k1_tarski('#skF_1'('#skF_3'))) != k1_tarski(k1_funct_1('#skF_3','#skF_2'('#skF_3')))
    | '#skF_2'('#skF_3') = '#skF_1'('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_10644,c_11952])).

tff(c_13390,plain,
    ( k1_tarski(k1_funct_1('#skF_3','#skF_2'('#skF_3'))) != k11_relat_1('#skF_3','#skF_1'('#skF_3'))
    | '#skF_2'('#skF_3') = '#skF_1'('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11479,c_13386])).

tff(c_13391,plain,(
    k1_tarski(k1_funct_1('#skF_3','#skF_2'('#skF_3'))) != k11_relat_1('#skF_3','#skF_1'('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_13390])).

tff(c_13396,plain,
    ( k11_relat_1('#skF_3','#skF_2'('#skF_3')) != k11_relat_1('#skF_3','#skF_1'('#skF_3'))
    | v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_310,c_13391])).

tff(c_13401,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_11189,c_13396])).

tff(c_13403,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_13401])).

%------------------------------------------------------------------------------
