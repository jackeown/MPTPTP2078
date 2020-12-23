%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:05 EST 2020

% Result     : Theorem 9.71s
% Output     : CNFRefutation 9.71s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 413 expanded)
%              Number of leaves         :   27 ( 159 expanded)
%              Depth                    :   16
%              Number of atoms          :  295 (1503 expanded)
%              Number of equality atoms :   31 (  98 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_connsp_2 > r2_hidden > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(m1_connsp_2,type,(
    m1_connsp_2: ( $i * $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_100,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                   => ( ( m1_connsp_2(C,A,B)
                        & m1_connsp_2(D,A,B) )
                    <=> m1_connsp_2(k9_subset_1(u1_struct_0(A),C,D),A,B) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_connsp_2)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => m1_subset_1(k9_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).

tff(f_77,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( m1_connsp_2(C,A,B)
              <=> r2_hidden(B,k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_connsp_2)).

tff(f_60,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => k9_subset_1(u1_struct_0(A),k1_tops_1(A,B),k1_tops_1(A,C)) = k1_tops_1(A,k9_subset_1(u1_struct_0(A),B,C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_tops_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k1_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tops_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(c_36,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_42,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_32,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_68,plain,(
    ! [A_52,B_53,C_54] :
      ( k9_subset_1(A_52,B_53,C_54) = k3_xboole_0(B_53,C_54)
      | ~ m1_subset_1(C_54,k1_zfmisc_1(A_52)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_76,plain,(
    ! [B_53] : k9_subset_1(u1_struct_0('#skF_3'),B_53,'#skF_6') = k3_xboole_0(B_53,'#skF_6') ),
    inference(resolution,[status(thm)],[c_32,c_68])).

tff(c_52,plain,
    ( m1_connsp_2('#skF_6','#skF_3','#skF_4')
    | m1_connsp_2(k9_subset_1(u1_struct_0('#skF_3'),'#skF_5','#skF_6'),'#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_58,plain,(
    m1_connsp_2(k9_subset_1(u1_struct_0('#skF_3'),'#skF_5','#skF_6'),'#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_78,plain,(
    m1_connsp_2(k3_xboole_0('#skF_5','#skF_6'),'#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_58])).

tff(c_44,plain,
    ( ~ m1_connsp_2(k9_subset_1(u1_struct_0('#skF_3'),'#skF_5','#skF_6'),'#skF_3','#skF_4')
    | ~ m1_connsp_2('#skF_6','#skF_3','#skF_4')
    | ~ m1_connsp_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_117,plain,
    ( ~ m1_connsp_2('#skF_6','#skF_3','#skF_4')
    | ~ m1_connsp_2('#skF_5','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_44])).

tff(c_118,plain,(
    ~ m1_connsp_2('#skF_5','#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_117])).

tff(c_40,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_38,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_34,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_79,plain,(
    ! [B_55] : k9_subset_1(u1_struct_0('#skF_3'),B_55,'#skF_6') = k3_xboole_0(B_55,'#skF_6') ),
    inference(resolution,[status(thm)],[c_32,c_68])).

tff(c_20,plain,(
    ! [A_7,B_8,C_9] :
      ( m1_subset_1(k9_subset_1(A_7,B_8,C_9),k1_zfmisc_1(A_7))
      | ~ m1_subset_1(C_9,k1_zfmisc_1(A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_85,plain,(
    ! [B_55] :
      ( m1_subset_1(k3_xboole_0(B_55,'#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_79,c_20])).

tff(c_91,plain,(
    ! [B_55] : m1_subset_1(k3_xboole_0(B_55,'#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_85])).

tff(c_1105,plain,(
    ! [B_164,A_165,C_166] :
      ( r2_hidden(B_164,k1_tops_1(A_165,C_166))
      | ~ m1_connsp_2(C_166,A_165,B_164)
      | ~ m1_subset_1(C_166,k1_zfmisc_1(u1_struct_0(A_165)))
      | ~ m1_subset_1(B_164,u1_struct_0(A_165))
      | ~ l1_pre_topc(A_165)
      | ~ v2_pre_topc(A_165)
      | v2_struct_0(A_165) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_1135,plain,(
    ! [B_164,B_55] :
      ( r2_hidden(B_164,k1_tops_1('#skF_3',k3_xboole_0(B_55,'#skF_6')))
      | ~ m1_connsp_2(k3_xboole_0(B_55,'#skF_6'),'#skF_3',B_164)
      | ~ m1_subset_1(B_164,u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_91,c_1105])).

tff(c_1198,plain,(
    ! [B_164,B_55] :
      ( r2_hidden(B_164,k1_tops_1('#skF_3',k3_xboole_0(B_55,'#skF_6')))
      | ~ m1_connsp_2(k3_xboole_0(B_55,'#skF_6'),'#skF_3',B_164)
      | ~ m1_subset_1(B_164,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_1135])).

tff(c_1199,plain,(
    ! [B_164,B_55] :
      ( r2_hidden(B_164,k1_tops_1('#skF_3',k3_xboole_0(B_55,'#skF_6')))
      | ~ m1_connsp_2(k3_xboole_0(B_55,'#skF_6'),'#skF_3',B_164)
      | ~ m1_subset_1(B_164,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_1198])).

tff(c_1599,plain,(
    ! [A_195,B_196,C_197] :
      ( k9_subset_1(u1_struct_0(A_195),k1_tops_1(A_195,B_196),k1_tops_1(A_195,C_197)) = k1_tops_1(A_195,k9_subset_1(u1_struct_0(A_195),B_196,C_197))
      | ~ m1_subset_1(C_197,k1_zfmisc_1(u1_struct_0(A_195)))
      | ~ m1_subset_1(B_196,k1_zfmisc_1(u1_struct_0(A_195)))
      | ~ l1_pre_topc(A_195)
      | ~ v2_pre_topc(A_195) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_155,plain,(
    ! [A_67,B_68] :
      ( m1_subset_1(k1_tops_1(A_67,B_68),k1_zfmisc_1(u1_struct_0(A_67)))
      | ~ m1_subset_1(B_68,k1_zfmisc_1(u1_struct_0(A_67)))
      | ~ l1_pre_topc(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_22,plain,(
    ! [A_10,B_11,C_12] :
      ( k9_subset_1(A_10,B_11,C_12) = k3_xboole_0(B_11,C_12)
      | ~ m1_subset_1(C_12,k1_zfmisc_1(A_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_481,plain,(
    ! [A_136,B_137,B_138] :
      ( k9_subset_1(u1_struct_0(A_136),B_137,k1_tops_1(A_136,B_138)) = k3_xboole_0(B_137,k1_tops_1(A_136,B_138))
      | ~ m1_subset_1(B_138,k1_zfmisc_1(u1_struct_0(A_136)))
      | ~ l1_pre_topc(A_136) ) ),
    inference(resolution,[status(thm)],[c_155,c_22])).

tff(c_504,plain,(
    ! [B_137] :
      ( k9_subset_1(u1_struct_0('#skF_3'),B_137,k1_tops_1('#skF_3','#skF_6')) = k3_xboole_0(B_137,k1_tops_1('#skF_3','#skF_6'))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_32,c_481])).

tff(c_535,plain,(
    ! [B_137] : k9_subset_1(u1_struct_0('#skF_3'),B_137,k1_tops_1('#skF_3','#skF_6')) = k3_xboole_0(B_137,k1_tops_1('#skF_3','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_504])).

tff(c_1642,plain,(
    ! [B_196] :
      ( k3_xboole_0(k1_tops_1('#skF_3',B_196),k1_tops_1('#skF_3','#skF_6')) = k1_tops_1('#skF_3',k9_subset_1(u1_struct_0('#skF_3'),B_196,'#skF_6'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(B_196,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1599,c_535])).

tff(c_1773,plain,(
    ! [B_199] :
      ( k3_xboole_0(k1_tops_1('#skF_3',B_199),k1_tops_1('#skF_3','#skF_6')) = k1_tops_1('#skF_3',k3_xboole_0(B_199,'#skF_6'))
      | ~ m1_subset_1(B_199,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_32,c_76,c_1642])).

tff(c_1866,plain,(
    k3_xboole_0(k1_tops_1('#skF_3','#skF_5'),k1_tops_1('#skF_3','#skF_6')) = k1_tops_1('#skF_3',k3_xboole_0('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_34,c_1773])).

tff(c_6,plain,(
    ! [D_6,A_1,B_2] :
      ( r2_hidden(D_6,A_1)
      | ~ r2_hidden(D_6,k3_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1978,plain,(
    ! [D_201] :
      ( r2_hidden(D_201,k1_tops_1('#skF_3','#skF_5'))
      | ~ r2_hidden(D_201,k1_tops_1('#skF_3',k3_xboole_0('#skF_5','#skF_6'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1866,c_6])).

tff(c_2110,plain,(
    ! [B_203] :
      ( r2_hidden(B_203,k1_tops_1('#skF_3','#skF_5'))
      | ~ m1_connsp_2(k3_xboole_0('#skF_5','#skF_6'),'#skF_3',B_203)
      | ~ m1_subset_1(B_203,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_1199,c_1978])).

tff(c_2113,plain,
    ( r2_hidden('#skF_4',k1_tops_1('#skF_3','#skF_5'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_78,c_2110])).

tff(c_2116,plain,(
    r2_hidden('#skF_4',k1_tops_1('#skF_3','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_2113])).

tff(c_28,plain,(
    ! [C_28,A_22,B_26] :
      ( m1_connsp_2(C_28,A_22,B_26)
      | ~ r2_hidden(B_26,k1_tops_1(A_22,C_28))
      | ~ m1_subset_1(C_28,k1_zfmisc_1(u1_struct_0(A_22)))
      | ~ m1_subset_1(B_26,u1_struct_0(A_22))
      | ~ l1_pre_topc(A_22)
      | ~ v2_pre_topc(A_22)
      | v2_struct_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_2197,plain,
    ( m1_connsp_2('#skF_5','#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_2116,c_28])).

tff(c_2200,plain,
    ( m1_connsp_2('#skF_5','#skF_3','#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_34,c_2197])).

tff(c_2202,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_118,c_2200])).

tff(c_2203,plain,(
    ~ m1_connsp_2('#skF_6','#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_117])).

tff(c_3133,plain,(
    ! [B_308,A_309,C_310] :
      ( r2_hidden(B_308,k1_tops_1(A_309,C_310))
      | ~ m1_connsp_2(C_310,A_309,B_308)
      | ~ m1_subset_1(C_310,k1_zfmisc_1(u1_struct_0(A_309)))
      | ~ m1_subset_1(B_308,u1_struct_0(A_309))
      | ~ l1_pre_topc(A_309)
      | ~ v2_pre_topc(A_309)
      | v2_struct_0(A_309) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_3161,plain,(
    ! [B_308,B_55] :
      ( r2_hidden(B_308,k1_tops_1('#skF_3',k3_xboole_0(B_55,'#skF_6')))
      | ~ m1_connsp_2(k3_xboole_0(B_55,'#skF_6'),'#skF_3',B_308)
      | ~ m1_subset_1(B_308,u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_91,c_3133])).

tff(c_3220,plain,(
    ! [B_308,B_55] :
      ( r2_hidden(B_308,k1_tops_1('#skF_3',k3_xboole_0(B_55,'#skF_6')))
      | ~ m1_connsp_2(k3_xboole_0(B_55,'#skF_6'),'#skF_3',B_308)
      | ~ m1_subset_1(B_308,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_3161])).

tff(c_3221,plain,(
    ! [B_308,B_55] :
      ( r2_hidden(B_308,k1_tops_1('#skF_3',k3_xboole_0(B_55,'#skF_6')))
      | ~ m1_connsp_2(k3_xboole_0(B_55,'#skF_6'),'#skF_3',B_308)
      | ~ m1_subset_1(B_308,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_3220])).

tff(c_3458,plain,(
    ! [A_325,B_326,C_327] :
      ( k9_subset_1(u1_struct_0(A_325),k1_tops_1(A_325,B_326),k1_tops_1(A_325,C_327)) = k1_tops_1(A_325,k9_subset_1(u1_struct_0(A_325),B_326,C_327))
      | ~ m1_subset_1(C_327,k1_zfmisc_1(u1_struct_0(A_325)))
      | ~ m1_subset_1(B_326,k1_zfmisc_1(u1_struct_0(A_325)))
      | ~ l1_pre_topc(A_325)
      | ~ v2_pre_topc(A_325) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_2241,plain,(
    ! [A_216,B_217] :
      ( m1_subset_1(k1_tops_1(A_216,B_217),k1_zfmisc_1(u1_struct_0(A_216)))
      | ~ m1_subset_1(B_217,k1_zfmisc_1(u1_struct_0(A_216)))
      | ~ l1_pre_topc(A_216) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_2476,plain,(
    ! [A_270,B_271,B_272] :
      ( k9_subset_1(u1_struct_0(A_270),B_271,k1_tops_1(A_270,B_272)) = k3_xboole_0(B_271,k1_tops_1(A_270,B_272))
      | ~ m1_subset_1(B_272,k1_zfmisc_1(u1_struct_0(A_270)))
      | ~ l1_pre_topc(A_270) ) ),
    inference(resolution,[status(thm)],[c_2241,c_22])).

tff(c_2497,plain,(
    ! [B_271] :
      ( k9_subset_1(u1_struct_0('#skF_3'),B_271,k1_tops_1('#skF_3','#skF_6')) = k3_xboole_0(B_271,k1_tops_1('#skF_3','#skF_6'))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_32,c_2476])).

tff(c_2525,plain,(
    ! [B_271] : k9_subset_1(u1_struct_0('#skF_3'),B_271,k1_tops_1('#skF_3','#skF_6')) = k3_xboole_0(B_271,k1_tops_1('#skF_3','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_2497])).

tff(c_3493,plain,(
    ! [B_326] :
      ( k3_xboole_0(k1_tops_1('#skF_3',B_326),k1_tops_1('#skF_3','#skF_6')) = k1_tops_1('#skF_3',k9_subset_1(u1_struct_0('#skF_3'),B_326,'#skF_6'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(B_326,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3458,c_2525])).

tff(c_5817,plain,(
    ! [B_384] :
      ( k3_xboole_0(k1_tops_1('#skF_3',B_384),k1_tops_1('#skF_3','#skF_6')) = k1_tops_1('#skF_3',k3_xboole_0(B_384,'#skF_6'))
      | ~ m1_subset_1(B_384,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_32,c_76,c_3493])).

tff(c_5938,plain,(
    k3_xboole_0(k1_tops_1('#skF_3','#skF_5'),k1_tops_1('#skF_3','#skF_6')) = k1_tops_1('#skF_3',k3_xboole_0('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_34,c_5817])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k3_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_6289,plain,(
    ! [D_390] :
      ( r2_hidden(D_390,k1_tops_1('#skF_3','#skF_6'))
      | ~ r2_hidden(D_390,k1_tops_1('#skF_3',k3_xboole_0('#skF_5','#skF_6'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5938,c_4])).

tff(c_6545,plain,(
    ! [B_393] :
      ( r2_hidden(B_393,k1_tops_1('#skF_3','#skF_6'))
      | ~ m1_connsp_2(k3_xboole_0('#skF_5','#skF_6'),'#skF_3',B_393)
      | ~ m1_subset_1(B_393,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_3221,c_6289])).

tff(c_6548,plain,
    ( r2_hidden('#skF_4',k1_tops_1('#skF_3','#skF_6'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_78,c_6545])).

tff(c_6551,plain,(
    r2_hidden('#skF_4',k1_tops_1('#skF_3','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_6548])).

tff(c_6553,plain,
    ( m1_connsp_2('#skF_6','#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_6551,c_28])).

tff(c_6556,plain,
    ( m1_connsp_2('#skF_6','#skF_3','#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_32,c_6553])).

tff(c_6558,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_2203,c_6556])).

tff(c_6559,plain,(
    m1_connsp_2('#skF_6','#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_7474,plain,(
    ! [B_497,A_498,C_499] :
      ( r2_hidden(B_497,k1_tops_1(A_498,C_499))
      | ~ m1_connsp_2(C_499,A_498,B_497)
      | ~ m1_subset_1(C_499,k1_zfmisc_1(u1_struct_0(A_498)))
      | ~ m1_subset_1(B_497,u1_struct_0(A_498))
      | ~ l1_pre_topc(A_498)
      | ~ v2_pre_topc(A_498)
      | v2_struct_0(A_498) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_7505,plain,(
    ! [B_497] :
      ( r2_hidden(B_497,k1_tops_1('#skF_3','#skF_6'))
      | ~ m1_connsp_2('#skF_6','#skF_3',B_497)
      | ~ m1_subset_1(B_497,u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_32,c_7474])).

tff(c_7560,plain,(
    ! [B_497] :
      ( r2_hidden(B_497,k1_tops_1('#skF_3','#skF_6'))
      | ~ m1_connsp_2('#skF_6','#skF_3',B_497)
      | ~ m1_subset_1(B_497,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_7505])).

tff(c_7561,plain,(
    ! [B_497] :
      ( r2_hidden(B_497,k1_tops_1('#skF_3','#skF_6'))
      | ~ m1_connsp_2('#skF_6','#skF_3',B_497)
      | ~ m1_subset_1(B_497,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_7560])).

tff(c_6570,plain,(
    ! [A_397,B_398,C_399] :
      ( k9_subset_1(A_397,B_398,C_399) = k3_xboole_0(B_398,C_399)
      | ~ m1_subset_1(C_399,k1_zfmisc_1(A_397)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_6578,plain,(
    ! [B_398] : k9_subset_1(u1_struct_0('#skF_3'),B_398,'#skF_6') = k3_xboole_0(B_398,'#skF_6') ),
    inference(resolution,[status(thm)],[c_32,c_6570])).

tff(c_6560,plain,(
    ~ m1_connsp_2(k9_subset_1(u1_struct_0('#skF_3'),'#skF_5','#skF_6'),'#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_6580,plain,(
    ~ m1_connsp_2(k3_xboole_0('#skF_5','#skF_6'),'#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6578,c_6560])).

tff(c_54,plain,
    ( m1_connsp_2('#skF_5','#skF_3','#skF_4')
    | m1_connsp_2(k9_subset_1(u1_struct_0('#skF_3'),'#skF_5','#skF_6'),'#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_6595,plain,
    ( m1_connsp_2('#skF_5','#skF_3','#skF_4')
    | m1_connsp_2(k3_xboole_0('#skF_5','#skF_6'),'#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6578,c_54])).

tff(c_6596,plain,(
    m1_connsp_2('#skF_5','#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_6580,c_6595])).

tff(c_7507,plain,(
    ! [B_497] :
      ( r2_hidden(B_497,k1_tops_1('#skF_3','#skF_5'))
      | ~ m1_connsp_2('#skF_5','#skF_3',B_497)
      | ~ m1_subset_1(B_497,u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_34,c_7474])).

tff(c_7564,plain,(
    ! [B_497] :
      ( r2_hidden(B_497,k1_tops_1('#skF_3','#skF_5'))
      | ~ m1_connsp_2('#skF_5','#skF_3',B_497)
      | ~ m1_subset_1(B_497,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_7507])).

tff(c_7565,plain,(
    ! [B_497] :
      ( r2_hidden(B_497,k1_tops_1('#skF_3','#skF_5'))
      | ~ m1_connsp_2('#skF_5','#skF_3',B_497)
      | ~ m1_subset_1(B_497,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_7564])).

tff(c_6581,plain,(
    ! [B_400] : k9_subset_1(u1_struct_0('#skF_3'),B_400,'#skF_6') = k3_xboole_0(B_400,'#skF_6') ),
    inference(resolution,[status(thm)],[c_32,c_6570])).

tff(c_6587,plain,(
    ! [B_400] :
      ( m1_subset_1(k3_xboole_0(B_400,'#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6581,c_20])).

tff(c_6593,plain,(
    ! [B_400] : m1_subset_1(k3_xboole_0(B_400,'#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_6587])).

tff(c_7977,plain,(
    ! [A_526,B_527,C_528] :
      ( k9_subset_1(u1_struct_0(A_526),k1_tops_1(A_526,B_527),k1_tops_1(A_526,C_528)) = k1_tops_1(A_526,k9_subset_1(u1_struct_0(A_526),B_527,C_528))
      | ~ m1_subset_1(C_528,k1_zfmisc_1(u1_struct_0(A_526)))
      | ~ m1_subset_1(B_527,k1_zfmisc_1(u1_struct_0(A_526)))
      | ~ l1_pre_topc(A_526)
      | ~ v2_pre_topc(A_526) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_6637,plain,(
    ! [A_408,B_409] :
      ( m1_subset_1(k1_tops_1(A_408,B_409),k1_zfmisc_1(u1_struct_0(A_408)))
      | ~ m1_subset_1(B_409,k1_zfmisc_1(u1_struct_0(A_408)))
      | ~ l1_pre_topc(A_408) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_6961,plain,(
    ! [A_473,B_474,B_475] :
      ( k9_subset_1(u1_struct_0(A_473),B_474,k1_tops_1(A_473,B_475)) = k3_xboole_0(B_474,k1_tops_1(A_473,B_475))
      | ~ m1_subset_1(B_475,k1_zfmisc_1(u1_struct_0(A_473)))
      | ~ l1_pre_topc(A_473) ) ),
    inference(resolution,[status(thm)],[c_6637,c_22])).

tff(c_6982,plain,(
    ! [B_474] :
      ( k9_subset_1(u1_struct_0('#skF_3'),B_474,k1_tops_1('#skF_3','#skF_6')) = k3_xboole_0(B_474,k1_tops_1('#skF_3','#skF_6'))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_32,c_6961])).

tff(c_7010,plain,(
    ! [B_474] : k9_subset_1(u1_struct_0('#skF_3'),B_474,k1_tops_1('#skF_3','#skF_6')) = k3_xboole_0(B_474,k1_tops_1('#skF_3','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_6982])).

tff(c_8012,plain,(
    ! [B_527] :
      ( k3_xboole_0(k1_tops_1('#skF_3',B_527),k1_tops_1('#skF_3','#skF_6')) = k1_tops_1('#skF_3',k9_subset_1(u1_struct_0('#skF_3'),B_527,'#skF_6'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(B_527,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7977,c_7010])).

tff(c_10362,plain,(
    ! [B_585] :
      ( k3_xboole_0(k1_tops_1('#skF_3',B_585),k1_tops_1('#skF_3','#skF_6')) = k1_tops_1('#skF_3',k3_xboole_0(B_585,'#skF_6'))
      | ~ m1_subset_1(B_585,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_32,c_6578,c_8012])).

tff(c_10491,plain,(
    k3_xboole_0(k1_tops_1('#skF_3','#skF_5'),k1_tops_1('#skF_3','#skF_6')) = k1_tops_1('#skF_3',k3_xboole_0('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_34,c_10362])).

tff(c_2,plain,(
    ! [D_6,A_1,B_2] :
      ( r2_hidden(D_6,k3_xboole_0(A_1,B_2))
      | ~ r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_14132,plain,(
    ! [D_641] :
      ( r2_hidden(D_641,k1_tops_1('#skF_3',k3_xboole_0('#skF_5','#skF_6')))
      | ~ r2_hidden(D_641,k1_tops_1('#skF_3','#skF_6'))
      | ~ r2_hidden(D_641,k1_tops_1('#skF_3','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10491,c_2])).

tff(c_14140,plain,(
    ! [D_641] :
      ( m1_connsp_2(k3_xboole_0('#skF_5','#skF_6'),'#skF_3',D_641)
      | ~ m1_subset_1(k3_xboole_0('#skF_5','#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(D_641,u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ r2_hidden(D_641,k1_tops_1('#skF_3','#skF_6'))
      | ~ r2_hidden(D_641,k1_tops_1('#skF_3','#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_14132,c_28])).

tff(c_14158,plain,(
    ! [D_641] :
      ( m1_connsp_2(k3_xboole_0('#skF_5','#skF_6'),'#skF_3',D_641)
      | ~ m1_subset_1(D_641,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3')
      | ~ r2_hidden(D_641,k1_tops_1('#skF_3','#skF_6'))
      | ~ r2_hidden(D_641,k1_tops_1('#skF_3','#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_6593,c_14140])).

tff(c_14529,plain,(
    ! [D_649] :
      ( m1_connsp_2(k3_xboole_0('#skF_5','#skF_6'),'#skF_3',D_649)
      | ~ m1_subset_1(D_649,u1_struct_0('#skF_3'))
      | ~ r2_hidden(D_649,k1_tops_1('#skF_3','#skF_6'))
      | ~ r2_hidden(D_649,k1_tops_1('#skF_3','#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_14158])).

tff(c_14538,plain,
    ( ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ r2_hidden('#skF_4',k1_tops_1('#skF_3','#skF_6'))
    | ~ r2_hidden('#skF_4',k1_tops_1('#skF_3','#skF_5')) ),
    inference(resolution,[status(thm)],[c_14529,c_6580])).

tff(c_14543,plain,
    ( ~ r2_hidden('#skF_4',k1_tops_1('#skF_3','#skF_6'))
    | ~ r2_hidden('#skF_4',k1_tops_1('#skF_3','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_14538])).

tff(c_14544,plain,(
    ~ r2_hidden('#skF_4',k1_tops_1('#skF_3','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_14543])).

tff(c_14547,plain,
    ( ~ m1_connsp_2('#skF_5','#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_7565,c_14544])).

tff(c_14551,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_6596,c_14547])).

tff(c_14552,plain,(
    ~ r2_hidden('#skF_4',k1_tops_1('#skF_3','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_14543])).

tff(c_14556,plain,
    ( ~ m1_connsp_2('#skF_6','#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_7561,c_14552])).

tff(c_14560,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_6559,c_14556])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n023.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 15:12:51 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.71/3.71  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.71/3.72  
% 9.71/3.72  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.71/3.72  %$ m1_connsp_2 > r2_hidden > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4
% 9.71/3.72  
% 9.71/3.72  %Foreground sorts:
% 9.71/3.72  
% 9.71/3.72  
% 9.71/3.72  %Background operators:
% 9.71/3.72  
% 9.71/3.72  
% 9.71/3.72  %Foreground operators:
% 9.71/3.72  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 9.71/3.72  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 9.71/3.72  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 9.71/3.72  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.71/3.72  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.71/3.72  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 9.71/3.72  tff('#skF_5', type, '#skF_5': $i).
% 9.71/3.72  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 9.71/3.72  tff('#skF_6', type, '#skF_6': $i).
% 9.71/3.72  tff('#skF_3', type, '#skF_3': $i).
% 9.71/3.72  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 9.71/3.72  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.71/3.72  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.71/3.72  tff('#skF_4', type, '#skF_4': $i).
% 9.71/3.72  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.71/3.72  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 9.71/3.72  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 9.71/3.72  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 9.71/3.72  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 9.71/3.72  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.71/3.72  
% 9.71/3.74  tff(f_100, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ((m1_connsp_2(C, A, B) & m1_connsp_2(D, A, B)) <=> m1_connsp_2(k9_subset_1(u1_struct_0(A), C, D), A, B)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_connsp_2)).
% 9.71/3.74  tff(f_42, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 9.71/3.74  tff(f_38, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => m1_subset_1(k9_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 9.71/3.74  tff(f_77, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m1_connsp_2(C, A, B) <=> r2_hidden(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_connsp_2)).
% 9.71/3.74  tff(f_60, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (k9_subset_1(u1_struct_0(A), k1_tops_1(A, B), k1_tops_1(A, C)) = k1_tops_1(A, k9_subset_1(u1_struct_0(A), B, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_tops_1)).
% 9.71/3.74  tff(f_48, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k1_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tops_1)).
% 9.71/3.74  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 9.71/3.74  tff(c_36, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_100])).
% 9.71/3.74  tff(c_42, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_100])).
% 9.71/3.74  tff(c_32, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_100])).
% 9.71/3.74  tff(c_68, plain, (![A_52, B_53, C_54]: (k9_subset_1(A_52, B_53, C_54)=k3_xboole_0(B_53, C_54) | ~m1_subset_1(C_54, k1_zfmisc_1(A_52)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 9.71/3.74  tff(c_76, plain, (![B_53]: (k9_subset_1(u1_struct_0('#skF_3'), B_53, '#skF_6')=k3_xboole_0(B_53, '#skF_6'))), inference(resolution, [status(thm)], [c_32, c_68])).
% 9.71/3.74  tff(c_52, plain, (m1_connsp_2('#skF_6', '#skF_3', '#skF_4') | m1_connsp_2(k9_subset_1(u1_struct_0('#skF_3'), '#skF_5', '#skF_6'), '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_100])).
% 9.71/3.74  tff(c_58, plain, (m1_connsp_2(k9_subset_1(u1_struct_0('#skF_3'), '#skF_5', '#skF_6'), '#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_52])).
% 9.71/3.74  tff(c_78, plain, (m1_connsp_2(k3_xboole_0('#skF_5', '#skF_6'), '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_58])).
% 9.71/3.74  tff(c_44, plain, (~m1_connsp_2(k9_subset_1(u1_struct_0('#skF_3'), '#skF_5', '#skF_6'), '#skF_3', '#skF_4') | ~m1_connsp_2('#skF_6', '#skF_3', '#skF_4') | ~m1_connsp_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_100])).
% 9.71/3.74  tff(c_117, plain, (~m1_connsp_2('#skF_6', '#skF_3', '#skF_4') | ~m1_connsp_2('#skF_5', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_44])).
% 9.71/3.74  tff(c_118, plain, (~m1_connsp_2('#skF_5', '#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_117])).
% 9.71/3.74  tff(c_40, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_100])).
% 9.71/3.74  tff(c_38, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_100])).
% 9.71/3.74  tff(c_34, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_100])).
% 9.71/3.74  tff(c_79, plain, (![B_55]: (k9_subset_1(u1_struct_0('#skF_3'), B_55, '#skF_6')=k3_xboole_0(B_55, '#skF_6'))), inference(resolution, [status(thm)], [c_32, c_68])).
% 9.71/3.74  tff(c_20, plain, (![A_7, B_8, C_9]: (m1_subset_1(k9_subset_1(A_7, B_8, C_9), k1_zfmisc_1(A_7)) | ~m1_subset_1(C_9, k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 9.71/3.74  tff(c_85, plain, (![B_55]: (m1_subset_1(k3_xboole_0(B_55, '#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(superposition, [status(thm), theory('equality')], [c_79, c_20])).
% 9.71/3.74  tff(c_91, plain, (![B_55]: (m1_subset_1(k3_xboole_0(B_55, '#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_85])).
% 9.71/3.74  tff(c_1105, plain, (![B_164, A_165, C_166]: (r2_hidden(B_164, k1_tops_1(A_165, C_166)) | ~m1_connsp_2(C_166, A_165, B_164) | ~m1_subset_1(C_166, k1_zfmisc_1(u1_struct_0(A_165))) | ~m1_subset_1(B_164, u1_struct_0(A_165)) | ~l1_pre_topc(A_165) | ~v2_pre_topc(A_165) | v2_struct_0(A_165))), inference(cnfTransformation, [status(thm)], [f_77])).
% 9.71/3.74  tff(c_1135, plain, (![B_164, B_55]: (r2_hidden(B_164, k1_tops_1('#skF_3', k3_xboole_0(B_55, '#skF_6'))) | ~m1_connsp_2(k3_xboole_0(B_55, '#skF_6'), '#skF_3', B_164) | ~m1_subset_1(B_164, u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_91, c_1105])).
% 9.71/3.74  tff(c_1198, plain, (![B_164, B_55]: (r2_hidden(B_164, k1_tops_1('#skF_3', k3_xboole_0(B_55, '#skF_6'))) | ~m1_connsp_2(k3_xboole_0(B_55, '#skF_6'), '#skF_3', B_164) | ~m1_subset_1(B_164, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_1135])).
% 9.71/3.74  tff(c_1199, plain, (![B_164, B_55]: (r2_hidden(B_164, k1_tops_1('#skF_3', k3_xboole_0(B_55, '#skF_6'))) | ~m1_connsp_2(k3_xboole_0(B_55, '#skF_6'), '#skF_3', B_164) | ~m1_subset_1(B_164, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_42, c_1198])).
% 9.71/3.74  tff(c_1599, plain, (![A_195, B_196, C_197]: (k9_subset_1(u1_struct_0(A_195), k1_tops_1(A_195, B_196), k1_tops_1(A_195, C_197))=k1_tops_1(A_195, k9_subset_1(u1_struct_0(A_195), B_196, C_197)) | ~m1_subset_1(C_197, k1_zfmisc_1(u1_struct_0(A_195))) | ~m1_subset_1(B_196, k1_zfmisc_1(u1_struct_0(A_195))) | ~l1_pre_topc(A_195) | ~v2_pre_topc(A_195))), inference(cnfTransformation, [status(thm)], [f_60])).
% 9.71/3.74  tff(c_155, plain, (![A_67, B_68]: (m1_subset_1(k1_tops_1(A_67, B_68), k1_zfmisc_1(u1_struct_0(A_67))) | ~m1_subset_1(B_68, k1_zfmisc_1(u1_struct_0(A_67))) | ~l1_pre_topc(A_67))), inference(cnfTransformation, [status(thm)], [f_48])).
% 9.71/3.74  tff(c_22, plain, (![A_10, B_11, C_12]: (k9_subset_1(A_10, B_11, C_12)=k3_xboole_0(B_11, C_12) | ~m1_subset_1(C_12, k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 9.71/3.74  tff(c_481, plain, (![A_136, B_137, B_138]: (k9_subset_1(u1_struct_0(A_136), B_137, k1_tops_1(A_136, B_138))=k3_xboole_0(B_137, k1_tops_1(A_136, B_138)) | ~m1_subset_1(B_138, k1_zfmisc_1(u1_struct_0(A_136))) | ~l1_pre_topc(A_136))), inference(resolution, [status(thm)], [c_155, c_22])).
% 9.71/3.74  tff(c_504, plain, (![B_137]: (k9_subset_1(u1_struct_0('#skF_3'), B_137, k1_tops_1('#skF_3', '#skF_6'))=k3_xboole_0(B_137, k1_tops_1('#skF_3', '#skF_6')) | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_32, c_481])).
% 9.71/3.74  tff(c_535, plain, (![B_137]: (k9_subset_1(u1_struct_0('#skF_3'), B_137, k1_tops_1('#skF_3', '#skF_6'))=k3_xboole_0(B_137, k1_tops_1('#skF_3', '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_504])).
% 9.71/3.74  tff(c_1642, plain, (![B_196]: (k3_xboole_0(k1_tops_1('#skF_3', B_196), k1_tops_1('#skF_3', '#skF_6'))=k1_tops_1('#skF_3', k9_subset_1(u1_struct_0('#skF_3'), B_196, '#skF_6')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1(B_196, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1599, c_535])).
% 9.71/3.74  tff(c_1773, plain, (![B_199]: (k3_xboole_0(k1_tops_1('#skF_3', B_199), k1_tops_1('#skF_3', '#skF_6'))=k1_tops_1('#skF_3', k3_xboole_0(B_199, '#skF_6')) | ~m1_subset_1(B_199, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_32, c_76, c_1642])).
% 9.71/3.74  tff(c_1866, plain, (k3_xboole_0(k1_tops_1('#skF_3', '#skF_5'), k1_tops_1('#skF_3', '#skF_6'))=k1_tops_1('#skF_3', k3_xboole_0('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_34, c_1773])).
% 9.71/3.74  tff(c_6, plain, (![D_6, A_1, B_2]: (r2_hidden(D_6, A_1) | ~r2_hidden(D_6, k3_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 9.71/3.74  tff(c_1978, plain, (![D_201]: (r2_hidden(D_201, k1_tops_1('#skF_3', '#skF_5')) | ~r2_hidden(D_201, k1_tops_1('#skF_3', k3_xboole_0('#skF_5', '#skF_6'))))), inference(superposition, [status(thm), theory('equality')], [c_1866, c_6])).
% 9.71/3.74  tff(c_2110, plain, (![B_203]: (r2_hidden(B_203, k1_tops_1('#skF_3', '#skF_5')) | ~m1_connsp_2(k3_xboole_0('#skF_5', '#skF_6'), '#skF_3', B_203) | ~m1_subset_1(B_203, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_1199, c_1978])).
% 9.71/3.74  tff(c_2113, plain, (r2_hidden('#skF_4', k1_tops_1('#skF_3', '#skF_5')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_78, c_2110])).
% 9.71/3.74  tff(c_2116, plain, (r2_hidden('#skF_4', k1_tops_1('#skF_3', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_2113])).
% 9.71/3.74  tff(c_28, plain, (![C_28, A_22, B_26]: (m1_connsp_2(C_28, A_22, B_26) | ~r2_hidden(B_26, k1_tops_1(A_22, C_28)) | ~m1_subset_1(C_28, k1_zfmisc_1(u1_struct_0(A_22))) | ~m1_subset_1(B_26, u1_struct_0(A_22)) | ~l1_pre_topc(A_22) | ~v2_pre_topc(A_22) | v2_struct_0(A_22))), inference(cnfTransformation, [status(thm)], [f_77])).
% 9.71/3.74  tff(c_2197, plain, (m1_connsp_2('#skF_5', '#skF_3', '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_2116, c_28])).
% 9.71/3.74  tff(c_2200, plain, (m1_connsp_2('#skF_5', '#skF_3', '#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_36, c_34, c_2197])).
% 9.71/3.74  tff(c_2202, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_118, c_2200])).
% 9.71/3.74  tff(c_2203, plain, (~m1_connsp_2('#skF_6', '#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_117])).
% 9.71/3.74  tff(c_3133, plain, (![B_308, A_309, C_310]: (r2_hidden(B_308, k1_tops_1(A_309, C_310)) | ~m1_connsp_2(C_310, A_309, B_308) | ~m1_subset_1(C_310, k1_zfmisc_1(u1_struct_0(A_309))) | ~m1_subset_1(B_308, u1_struct_0(A_309)) | ~l1_pre_topc(A_309) | ~v2_pre_topc(A_309) | v2_struct_0(A_309))), inference(cnfTransformation, [status(thm)], [f_77])).
% 9.71/3.74  tff(c_3161, plain, (![B_308, B_55]: (r2_hidden(B_308, k1_tops_1('#skF_3', k3_xboole_0(B_55, '#skF_6'))) | ~m1_connsp_2(k3_xboole_0(B_55, '#skF_6'), '#skF_3', B_308) | ~m1_subset_1(B_308, u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_91, c_3133])).
% 9.71/3.74  tff(c_3220, plain, (![B_308, B_55]: (r2_hidden(B_308, k1_tops_1('#skF_3', k3_xboole_0(B_55, '#skF_6'))) | ~m1_connsp_2(k3_xboole_0(B_55, '#skF_6'), '#skF_3', B_308) | ~m1_subset_1(B_308, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_3161])).
% 9.71/3.74  tff(c_3221, plain, (![B_308, B_55]: (r2_hidden(B_308, k1_tops_1('#skF_3', k3_xboole_0(B_55, '#skF_6'))) | ~m1_connsp_2(k3_xboole_0(B_55, '#skF_6'), '#skF_3', B_308) | ~m1_subset_1(B_308, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_42, c_3220])).
% 9.71/3.74  tff(c_3458, plain, (![A_325, B_326, C_327]: (k9_subset_1(u1_struct_0(A_325), k1_tops_1(A_325, B_326), k1_tops_1(A_325, C_327))=k1_tops_1(A_325, k9_subset_1(u1_struct_0(A_325), B_326, C_327)) | ~m1_subset_1(C_327, k1_zfmisc_1(u1_struct_0(A_325))) | ~m1_subset_1(B_326, k1_zfmisc_1(u1_struct_0(A_325))) | ~l1_pre_topc(A_325) | ~v2_pre_topc(A_325))), inference(cnfTransformation, [status(thm)], [f_60])).
% 9.71/3.74  tff(c_2241, plain, (![A_216, B_217]: (m1_subset_1(k1_tops_1(A_216, B_217), k1_zfmisc_1(u1_struct_0(A_216))) | ~m1_subset_1(B_217, k1_zfmisc_1(u1_struct_0(A_216))) | ~l1_pre_topc(A_216))), inference(cnfTransformation, [status(thm)], [f_48])).
% 9.71/3.74  tff(c_2476, plain, (![A_270, B_271, B_272]: (k9_subset_1(u1_struct_0(A_270), B_271, k1_tops_1(A_270, B_272))=k3_xboole_0(B_271, k1_tops_1(A_270, B_272)) | ~m1_subset_1(B_272, k1_zfmisc_1(u1_struct_0(A_270))) | ~l1_pre_topc(A_270))), inference(resolution, [status(thm)], [c_2241, c_22])).
% 9.71/3.74  tff(c_2497, plain, (![B_271]: (k9_subset_1(u1_struct_0('#skF_3'), B_271, k1_tops_1('#skF_3', '#skF_6'))=k3_xboole_0(B_271, k1_tops_1('#skF_3', '#skF_6')) | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_32, c_2476])).
% 9.71/3.74  tff(c_2525, plain, (![B_271]: (k9_subset_1(u1_struct_0('#skF_3'), B_271, k1_tops_1('#skF_3', '#skF_6'))=k3_xboole_0(B_271, k1_tops_1('#skF_3', '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_2497])).
% 9.71/3.74  tff(c_3493, plain, (![B_326]: (k3_xboole_0(k1_tops_1('#skF_3', B_326), k1_tops_1('#skF_3', '#skF_6'))=k1_tops_1('#skF_3', k9_subset_1(u1_struct_0('#skF_3'), B_326, '#skF_6')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1(B_326, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_3458, c_2525])).
% 9.71/3.74  tff(c_5817, plain, (![B_384]: (k3_xboole_0(k1_tops_1('#skF_3', B_384), k1_tops_1('#skF_3', '#skF_6'))=k1_tops_1('#skF_3', k3_xboole_0(B_384, '#skF_6')) | ~m1_subset_1(B_384, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_32, c_76, c_3493])).
% 9.71/3.74  tff(c_5938, plain, (k3_xboole_0(k1_tops_1('#skF_3', '#skF_5'), k1_tops_1('#skF_3', '#skF_6'))=k1_tops_1('#skF_3', k3_xboole_0('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_34, c_5817])).
% 9.71/3.74  tff(c_4, plain, (![D_6, B_2, A_1]: (r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k3_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 9.71/3.74  tff(c_6289, plain, (![D_390]: (r2_hidden(D_390, k1_tops_1('#skF_3', '#skF_6')) | ~r2_hidden(D_390, k1_tops_1('#skF_3', k3_xboole_0('#skF_5', '#skF_6'))))), inference(superposition, [status(thm), theory('equality')], [c_5938, c_4])).
% 9.71/3.74  tff(c_6545, plain, (![B_393]: (r2_hidden(B_393, k1_tops_1('#skF_3', '#skF_6')) | ~m1_connsp_2(k3_xboole_0('#skF_5', '#skF_6'), '#skF_3', B_393) | ~m1_subset_1(B_393, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_3221, c_6289])).
% 9.71/3.74  tff(c_6548, plain, (r2_hidden('#skF_4', k1_tops_1('#skF_3', '#skF_6')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_78, c_6545])).
% 9.71/3.74  tff(c_6551, plain, (r2_hidden('#skF_4', k1_tops_1('#skF_3', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_6548])).
% 9.71/3.74  tff(c_6553, plain, (m1_connsp_2('#skF_6', '#skF_3', '#skF_4') | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_6551, c_28])).
% 9.71/3.74  tff(c_6556, plain, (m1_connsp_2('#skF_6', '#skF_3', '#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_36, c_32, c_6553])).
% 9.71/3.74  tff(c_6558, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_2203, c_6556])).
% 9.71/3.74  tff(c_6559, plain, (m1_connsp_2('#skF_6', '#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_52])).
% 9.71/3.74  tff(c_7474, plain, (![B_497, A_498, C_499]: (r2_hidden(B_497, k1_tops_1(A_498, C_499)) | ~m1_connsp_2(C_499, A_498, B_497) | ~m1_subset_1(C_499, k1_zfmisc_1(u1_struct_0(A_498))) | ~m1_subset_1(B_497, u1_struct_0(A_498)) | ~l1_pre_topc(A_498) | ~v2_pre_topc(A_498) | v2_struct_0(A_498))), inference(cnfTransformation, [status(thm)], [f_77])).
% 9.71/3.74  tff(c_7505, plain, (![B_497]: (r2_hidden(B_497, k1_tops_1('#skF_3', '#skF_6')) | ~m1_connsp_2('#skF_6', '#skF_3', B_497) | ~m1_subset_1(B_497, u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_32, c_7474])).
% 9.71/3.74  tff(c_7560, plain, (![B_497]: (r2_hidden(B_497, k1_tops_1('#skF_3', '#skF_6')) | ~m1_connsp_2('#skF_6', '#skF_3', B_497) | ~m1_subset_1(B_497, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_7505])).
% 9.71/3.74  tff(c_7561, plain, (![B_497]: (r2_hidden(B_497, k1_tops_1('#skF_3', '#skF_6')) | ~m1_connsp_2('#skF_6', '#skF_3', B_497) | ~m1_subset_1(B_497, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_42, c_7560])).
% 9.71/3.74  tff(c_6570, plain, (![A_397, B_398, C_399]: (k9_subset_1(A_397, B_398, C_399)=k3_xboole_0(B_398, C_399) | ~m1_subset_1(C_399, k1_zfmisc_1(A_397)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 9.71/3.74  tff(c_6578, plain, (![B_398]: (k9_subset_1(u1_struct_0('#skF_3'), B_398, '#skF_6')=k3_xboole_0(B_398, '#skF_6'))), inference(resolution, [status(thm)], [c_32, c_6570])).
% 9.71/3.74  tff(c_6560, plain, (~m1_connsp_2(k9_subset_1(u1_struct_0('#skF_3'), '#skF_5', '#skF_6'), '#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_52])).
% 9.71/3.74  tff(c_6580, plain, (~m1_connsp_2(k3_xboole_0('#skF_5', '#skF_6'), '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6578, c_6560])).
% 9.71/3.74  tff(c_54, plain, (m1_connsp_2('#skF_5', '#skF_3', '#skF_4') | m1_connsp_2(k9_subset_1(u1_struct_0('#skF_3'), '#skF_5', '#skF_6'), '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_100])).
% 9.71/3.74  tff(c_6595, plain, (m1_connsp_2('#skF_5', '#skF_3', '#skF_4') | m1_connsp_2(k3_xboole_0('#skF_5', '#skF_6'), '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6578, c_54])).
% 9.71/3.74  tff(c_6596, plain, (m1_connsp_2('#skF_5', '#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_6580, c_6595])).
% 9.71/3.74  tff(c_7507, plain, (![B_497]: (r2_hidden(B_497, k1_tops_1('#skF_3', '#skF_5')) | ~m1_connsp_2('#skF_5', '#skF_3', B_497) | ~m1_subset_1(B_497, u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_34, c_7474])).
% 9.71/3.74  tff(c_7564, plain, (![B_497]: (r2_hidden(B_497, k1_tops_1('#skF_3', '#skF_5')) | ~m1_connsp_2('#skF_5', '#skF_3', B_497) | ~m1_subset_1(B_497, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_7507])).
% 9.71/3.74  tff(c_7565, plain, (![B_497]: (r2_hidden(B_497, k1_tops_1('#skF_3', '#skF_5')) | ~m1_connsp_2('#skF_5', '#skF_3', B_497) | ~m1_subset_1(B_497, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_42, c_7564])).
% 9.71/3.74  tff(c_6581, plain, (![B_400]: (k9_subset_1(u1_struct_0('#skF_3'), B_400, '#skF_6')=k3_xboole_0(B_400, '#skF_6'))), inference(resolution, [status(thm)], [c_32, c_6570])).
% 9.71/3.74  tff(c_6587, plain, (![B_400]: (m1_subset_1(k3_xboole_0(B_400, '#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(superposition, [status(thm), theory('equality')], [c_6581, c_20])).
% 9.71/3.74  tff(c_6593, plain, (![B_400]: (m1_subset_1(k3_xboole_0(B_400, '#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_6587])).
% 9.71/3.74  tff(c_7977, plain, (![A_526, B_527, C_528]: (k9_subset_1(u1_struct_0(A_526), k1_tops_1(A_526, B_527), k1_tops_1(A_526, C_528))=k1_tops_1(A_526, k9_subset_1(u1_struct_0(A_526), B_527, C_528)) | ~m1_subset_1(C_528, k1_zfmisc_1(u1_struct_0(A_526))) | ~m1_subset_1(B_527, k1_zfmisc_1(u1_struct_0(A_526))) | ~l1_pre_topc(A_526) | ~v2_pre_topc(A_526))), inference(cnfTransformation, [status(thm)], [f_60])).
% 9.71/3.74  tff(c_6637, plain, (![A_408, B_409]: (m1_subset_1(k1_tops_1(A_408, B_409), k1_zfmisc_1(u1_struct_0(A_408))) | ~m1_subset_1(B_409, k1_zfmisc_1(u1_struct_0(A_408))) | ~l1_pre_topc(A_408))), inference(cnfTransformation, [status(thm)], [f_48])).
% 9.71/3.74  tff(c_6961, plain, (![A_473, B_474, B_475]: (k9_subset_1(u1_struct_0(A_473), B_474, k1_tops_1(A_473, B_475))=k3_xboole_0(B_474, k1_tops_1(A_473, B_475)) | ~m1_subset_1(B_475, k1_zfmisc_1(u1_struct_0(A_473))) | ~l1_pre_topc(A_473))), inference(resolution, [status(thm)], [c_6637, c_22])).
% 9.71/3.74  tff(c_6982, plain, (![B_474]: (k9_subset_1(u1_struct_0('#skF_3'), B_474, k1_tops_1('#skF_3', '#skF_6'))=k3_xboole_0(B_474, k1_tops_1('#skF_3', '#skF_6')) | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_32, c_6961])).
% 9.71/3.74  tff(c_7010, plain, (![B_474]: (k9_subset_1(u1_struct_0('#skF_3'), B_474, k1_tops_1('#skF_3', '#skF_6'))=k3_xboole_0(B_474, k1_tops_1('#skF_3', '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_6982])).
% 9.71/3.74  tff(c_8012, plain, (![B_527]: (k3_xboole_0(k1_tops_1('#skF_3', B_527), k1_tops_1('#skF_3', '#skF_6'))=k1_tops_1('#skF_3', k9_subset_1(u1_struct_0('#skF_3'), B_527, '#skF_6')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1(B_527, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_7977, c_7010])).
% 9.71/3.74  tff(c_10362, plain, (![B_585]: (k3_xboole_0(k1_tops_1('#skF_3', B_585), k1_tops_1('#skF_3', '#skF_6'))=k1_tops_1('#skF_3', k3_xboole_0(B_585, '#skF_6')) | ~m1_subset_1(B_585, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_32, c_6578, c_8012])).
% 9.71/3.74  tff(c_10491, plain, (k3_xboole_0(k1_tops_1('#skF_3', '#skF_5'), k1_tops_1('#skF_3', '#skF_6'))=k1_tops_1('#skF_3', k3_xboole_0('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_34, c_10362])).
% 9.71/3.74  tff(c_2, plain, (![D_6, A_1, B_2]: (r2_hidden(D_6, k3_xboole_0(A_1, B_2)) | ~r2_hidden(D_6, B_2) | ~r2_hidden(D_6, A_1))), inference(cnfTransformation, [status(thm)], [f_34])).
% 9.71/3.74  tff(c_14132, plain, (![D_641]: (r2_hidden(D_641, k1_tops_1('#skF_3', k3_xboole_0('#skF_5', '#skF_6'))) | ~r2_hidden(D_641, k1_tops_1('#skF_3', '#skF_6')) | ~r2_hidden(D_641, k1_tops_1('#skF_3', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_10491, c_2])).
% 9.71/3.74  tff(c_14140, plain, (![D_641]: (m1_connsp_2(k3_xboole_0('#skF_5', '#skF_6'), '#skF_3', D_641) | ~m1_subset_1(k3_xboole_0('#skF_5', '#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1(D_641, u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~r2_hidden(D_641, k1_tops_1('#skF_3', '#skF_6')) | ~r2_hidden(D_641, k1_tops_1('#skF_3', '#skF_5')))), inference(resolution, [status(thm)], [c_14132, c_28])).
% 9.71/3.74  tff(c_14158, plain, (![D_641]: (m1_connsp_2(k3_xboole_0('#skF_5', '#skF_6'), '#skF_3', D_641) | ~m1_subset_1(D_641, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3') | ~r2_hidden(D_641, k1_tops_1('#skF_3', '#skF_6')) | ~r2_hidden(D_641, k1_tops_1('#skF_3', '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_6593, c_14140])).
% 9.71/3.74  tff(c_14529, plain, (![D_649]: (m1_connsp_2(k3_xboole_0('#skF_5', '#skF_6'), '#skF_3', D_649) | ~m1_subset_1(D_649, u1_struct_0('#skF_3')) | ~r2_hidden(D_649, k1_tops_1('#skF_3', '#skF_6')) | ~r2_hidden(D_649, k1_tops_1('#skF_3', '#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_42, c_14158])).
% 9.71/3.74  tff(c_14538, plain, (~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~r2_hidden('#skF_4', k1_tops_1('#skF_3', '#skF_6')) | ~r2_hidden('#skF_4', k1_tops_1('#skF_3', '#skF_5'))), inference(resolution, [status(thm)], [c_14529, c_6580])).
% 9.71/3.74  tff(c_14543, plain, (~r2_hidden('#skF_4', k1_tops_1('#skF_3', '#skF_6')) | ~r2_hidden('#skF_4', k1_tops_1('#skF_3', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_14538])).
% 9.71/3.74  tff(c_14544, plain, (~r2_hidden('#skF_4', k1_tops_1('#skF_3', '#skF_5'))), inference(splitLeft, [status(thm)], [c_14543])).
% 9.71/3.74  tff(c_14547, plain, (~m1_connsp_2('#skF_5', '#skF_3', '#skF_4') | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_7565, c_14544])).
% 9.71/3.74  tff(c_14551, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_6596, c_14547])).
% 9.71/3.74  tff(c_14552, plain, (~r2_hidden('#skF_4', k1_tops_1('#skF_3', '#skF_6'))), inference(splitRight, [status(thm)], [c_14543])).
% 9.71/3.74  tff(c_14556, plain, (~m1_connsp_2('#skF_6', '#skF_3', '#skF_4') | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_7561, c_14552])).
% 9.71/3.74  tff(c_14560, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_6559, c_14556])).
% 9.71/3.74  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.71/3.74  
% 9.71/3.74  Inference rules
% 9.71/3.74  ----------------------
% 9.71/3.74  #Ref     : 0
% 9.71/3.74  #Sup     : 3129
% 9.71/3.74  #Fact    : 0
% 9.71/3.74  #Define  : 0
% 9.71/3.74  #Split   : 11
% 9.71/3.74  #Chain   : 0
% 9.71/3.74  #Close   : 0
% 9.71/3.74  
% 9.71/3.74  Ordering : KBO
% 9.71/3.74  
% 9.71/3.74  Simplification rules
% 9.71/3.74  ----------------------
% 9.71/3.74  #Subsume      : 145
% 9.71/3.74  #Demod        : 2191
% 9.71/3.74  #Tautology    : 462
% 9.71/3.74  #SimpNegUnit  : 140
% 9.71/3.74  #BackRed      : 2
% 9.71/3.75  
% 9.71/3.75  #Partial instantiations: 0
% 9.71/3.75  #Strategies tried      : 1
% 9.71/3.75  
% 9.71/3.75  Timing (in seconds)
% 9.71/3.75  ----------------------
% 9.71/3.75  Preprocessing        : 0.32
% 9.71/3.75  Parsing              : 0.17
% 9.71/3.75  CNF conversion       : 0.03
% 9.71/3.75  Main loop            : 2.63
% 9.71/3.75  Inferencing          : 0.72
% 9.71/3.75  Reduction            : 1.01
% 9.71/3.75  Demodulation         : 0.80
% 9.71/3.75  BG Simplification    : 0.11
% 9.71/3.75  Subsumption          : 0.61
% 9.71/3.75  Abstraction          : 0.17
% 9.71/3.75  MUC search           : 0.00
% 9.71/3.75  Cooper               : 0.00
% 9.71/3.75  Total                : 3.00
% 9.71/3.75  Index Insertion      : 0.00
% 9.71/3.75  Index Deletion       : 0.00
% 9.71/3.75  Index Matching       : 0.00
% 9.71/3.75  BG Taut test         : 0.00
%------------------------------------------------------------------------------
