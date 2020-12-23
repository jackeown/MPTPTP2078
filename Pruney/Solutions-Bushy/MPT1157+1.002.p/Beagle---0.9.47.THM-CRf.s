%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1157+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:31 EST 2020

% Result     : Theorem 4.78s
% Output     : CNFRefutation 5.15s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 480 expanded)
%              Number of leaves         :   34 ( 179 expanded)
%              Depth                    :   19
%              Number of atoms          :  258 (1685 expanded)
%              Number of equality atoms :   29 ( 150 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k6_domain_1 > k1_orders_2 > a_2_0_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff(k1_orders_2,type,(
    k1_orders_2: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(a_2_0_orders_2,type,(
    a_2_0_orders_2: ( $i * $i ) > $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(r2_orders_2,type,(
    r2_orders_2: ( $i * $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_139,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ( r2_orders_2(A,B,C)
                <=> r2_hidden(C,k1_orders_2(A,k6_domain_1(u1_struct_0(A),B))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_orders_2)).

tff(f_58,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_100,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_66,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_54,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_40,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_orders_2(A,B) = a_2_0_orders_2(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_orders_2)).

tff(f_47,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_93,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(B)
        & v3_orders_2(B)
        & v4_orders_2(B)
        & v5_orders_2(B)
        & l1_orders_2(B)
        & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B))) )
     => ( r2_hidden(A,a_2_0_orders_2(B,C))
      <=> ? [D] :
            ( m1_subset_1(D,u1_struct_0(B))
            & A = D
            & ! [E] :
                ( m1_subset_1(E,u1_struct_0(B))
               => ( r2_hidden(E,C)
                 => r2_orders_2(B,E,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_0_orders_2)).

tff(c_54,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_52,plain,(
    v3_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_50,plain,(
    v4_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_48,plain,(
    v5_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_46,plain,(
    l1_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_18,plain,(
    ! [A_11] :
      ( l1_struct_0(A_11)
      | ~ l1_orders_2(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_42,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_1264,plain,(
    ! [A_157,B_158] :
      ( k6_domain_1(A_157,B_158) = k1_tarski(B_158)
      | ~ m1_subset_1(B_158,A_157)
      | v1_xboole_0(A_157) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_1271,plain,
    ( k6_domain_1(u1_struct_0('#skF_5'),'#skF_7') = k1_tarski('#skF_7')
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_42,c_1264])).

tff(c_1273,plain,(
    v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_1271])).

tff(c_20,plain,(
    ! [A_12] :
      ( ~ v1_xboole_0(u1_struct_0(A_12))
      | ~ l1_struct_0(A_12)
      | v2_struct_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_1276,plain,
    ( ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_1273,c_20])).

tff(c_1279,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_1276])).

tff(c_1282,plain,(
    ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_18,c_1279])).

tff(c_1286,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_1282])).

tff(c_1288,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_1271])).

tff(c_44,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_1272,plain,
    ( k6_domain_1(u1_struct_0('#skF_5'),'#skF_6') = k1_tarski('#skF_6')
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_44,c_1264])).

tff(c_1294,plain,(
    k6_domain_1(u1_struct_0('#skF_5'),'#skF_6') = k1_tarski('#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_1288,c_1272])).

tff(c_1306,plain,(
    ! [A_162,B_163] :
      ( m1_subset_1(k6_domain_1(A_162,B_163),k1_zfmisc_1(A_162))
      | ~ m1_subset_1(B_163,A_162)
      | v1_xboole_0(A_162) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_1314,plain,
    ( m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1294,c_1306])).

tff(c_1321,plain,
    ( m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_1314])).

tff(c_1322,plain,(
    m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_1288,c_1321])).

tff(c_1528,plain,(
    ! [A_192,B_193] :
      ( k1_orders_2(A_192,B_193) = a_2_0_orders_2(A_192,B_193)
      | ~ m1_subset_1(B_193,k1_zfmisc_1(u1_struct_0(A_192)))
      | ~ l1_orders_2(A_192)
      | ~ v5_orders_2(A_192)
      | ~ v4_orders_2(A_192)
      | ~ v3_orders_2(A_192)
      | v2_struct_0(A_192) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_1534,plain,
    ( k1_orders_2('#skF_5',k1_tarski('#skF_6')) = a_2_0_orders_2('#skF_5',k1_tarski('#skF_6'))
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_1322,c_1528])).

tff(c_1545,plain,
    ( k1_orders_2('#skF_5',k1_tarski('#skF_6')) = a_2_0_orders_2('#skF_5',k1_tarski('#skF_6'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_1534])).

tff(c_1546,plain,(
    k1_orders_2('#skF_5',k1_tarski('#skF_6')) = a_2_0_orders_2('#skF_5',k1_tarski('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_1545])).

tff(c_56,plain,
    ( ~ r2_hidden('#skF_7',k1_orders_2('#skF_5',k6_domain_1(u1_struct_0('#skF_5'),'#skF_6')))
    | ~ r2_orders_2('#skF_5','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_65,plain,(
    ~ r2_orders_2('#skF_5','#skF_6','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_6,plain,(
    ! [C_8] : r2_hidden(C_8,k1_tarski(C_8)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_92,plain,(
    ! [A_51,B_52] :
      ( k6_domain_1(A_51,B_52) = k1_tarski(B_52)
      | ~ m1_subset_1(B_52,A_51)
      | v1_xboole_0(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_99,plain,
    ( k6_domain_1(u1_struct_0('#skF_5'),'#skF_7') = k1_tarski('#skF_7')
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_42,c_92])).

tff(c_101,plain,(
    v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_99])).

tff(c_109,plain,
    ( ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_101,c_20])).

tff(c_112,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_109])).

tff(c_115,plain,(
    ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_18,c_112])).

tff(c_119,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_115])).

tff(c_121,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_99])).

tff(c_100,plain,
    ( k6_domain_1(u1_struct_0('#skF_5'),'#skF_6') = k1_tarski('#skF_6')
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_44,c_92])).

tff(c_126,plain,(
    k6_domain_1(u1_struct_0('#skF_5'),'#skF_6') = k1_tarski('#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_121,c_100])).

tff(c_132,plain,(
    ! [A_56,B_57] :
      ( m1_subset_1(k6_domain_1(A_56,B_57),k1_zfmisc_1(A_56))
      | ~ m1_subset_1(B_57,A_56)
      | v1_xboole_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_140,plain,
    ( m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_126,c_132])).

tff(c_147,plain,
    ( m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_140])).

tff(c_148,plain,(
    m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_121,c_147])).

tff(c_281,plain,(
    ! [A_75,B_76] :
      ( k1_orders_2(A_75,B_76) = a_2_0_orders_2(A_75,B_76)
      | ~ m1_subset_1(B_76,k1_zfmisc_1(u1_struct_0(A_75)))
      | ~ l1_orders_2(A_75)
      | ~ v5_orders_2(A_75)
      | ~ v4_orders_2(A_75)
      | ~ v3_orders_2(A_75)
      | v2_struct_0(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_287,plain,
    ( k1_orders_2('#skF_5',k1_tarski('#skF_6')) = a_2_0_orders_2('#skF_5',k1_tarski('#skF_6'))
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_148,c_281])).

tff(c_298,plain,
    ( k1_orders_2('#skF_5',k1_tarski('#skF_6')) = a_2_0_orders_2('#skF_5',k1_tarski('#skF_6'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_287])).

tff(c_299,plain,(
    k1_orders_2('#skF_5',k1_tarski('#skF_6')) = a_2_0_orders_2('#skF_5',k1_tarski('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_298])).

tff(c_62,plain,
    ( r2_orders_2('#skF_5','#skF_6','#skF_7')
    | r2_hidden('#skF_7',k1_orders_2('#skF_5',k6_domain_1(u1_struct_0('#skF_5'),'#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_166,plain,
    ( r2_orders_2('#skF_5','#skF_6','#skF_7')
    | r2_hidden('#skF_7',k1_orders_2('#skF_5',k1_tarski('#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_62])).

tff(c_167,plain,(
    r2_hidden('#skF_7',k1_orders_2('#skF_5',k1_tarski('#skF_6'))) ),
    inference(negUnitSimplification,[status(thm)],[c_65,c_166])).

tff(c_306,plain,(
    r2_hidden('#skF_7',a_2_0_orders_2('#skF_5',k1_tarski('#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_299,c_167])).

tff(c_393,plain,(
    ! [A_86,B_87,C_88] :
      ( '#skF_3'(A_86,B_87,C_88) = A_86
      | ~ r2_hidden(A_86,a_2_0_orders_2(B_87,C_88))
      | ~ m1_subset_1(C_88,k1_zfmisc_1(u1_struct_0(B_87)))
      | ~ l1_orders_2(B_87)
      | ~ v5_orders_2(B_87)
      | ~ v4_orders_2(B_87)
      | ~ v3_orders_2(B_87)
      | v2_struct_0(B_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_395,plain,
    ( '#skF_3'('#skF_7','#skF_5',k1_tarski('#skF_6')) = '#skF_7'
    | ~ m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_306,c_393])).

tff(c_407,plain,
    ( '#skF_3'('#skF_7','#skF_5',k1_tarski('#skF_6')) = '#skF_7'
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_148,c_395])).

tff(c_408,plain,(
    '#skF_3'('#skF_7','#skF_5',k1_tarski('#skF_6')) = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_407])).

tff(c_1096,plain,(
    ! [B_139,E_140,A_141,C_142] :
      ( r2_orders_2(B_139,E_140,'#skF_3'(A_141,B_139,C_142))
      | ~ r2_hidden(E_140,C_142)
      | ~ m1_subset_1(E_140,u1_struct_0(B_139))
      | ~ r2_hidden(A_141,a_2_0_orders_2(B_139,C_142))
      | ~ m1_subset_1(C_142,k1_zfmisc_1(u1_struct_0(B_139)))
      | ~ l1_orders_2(B_139)
      | ~ v5_orders_2(B_139)
      | ~ v4_orders_2(B_139)
      | ~ v3_orders_2(B_139)
      | v2_struct_0(B_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_1103,plain,(
    ! [E_140,A_141] :
      ( r2_orders_2('#skF_5',E_140,'#skF_3'(A_141,'#skF_5',k1_tarski('#skF_6')))
      | ~ r2_hidden(E_140,k1_tarski('#skF_6'))
      | ~ m1_subset_1(E_140,u1_struct_0('#skF_5'))
      | ~ r2_hidden(A_141,a_2_0_orders_2('#skF_5',k1_tarski('#skF_6')))
      | ~ l1_orders_2('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | ~ v4_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_148,c_1096])).

tff(c_1114,plain,(
    ! [E_140,A_141] :
      ( r2_orders_2('#skF_5',E_140,'#skF_3'(A_141,'#skF_5',k1_tarski('#skF_6')))
      | ~ r2_hidden(E_140,k1_tarski('#skF_6'))
      | ~ m1_subset_1(E_140,u1_struct_0('#skF_5'))
      | ~ r2_hidden(A_141,a_2_0_orders_2('#skF_5',k1_tarski('#skF_6')))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_1103])).

tff(c_1186,plain,(
    ! [E_144,A_145] :
      ( r2_orders_2('#skF_5',E_144,'#skF_3'(A_145,'#skF_5',k1_tarski('#skF_6')))
      | ~ r2_hidden(E_144,k1_tarski('#skF_6'))
      | ~ m1_subset_1(E_144,u1_struct_0('#skF_5'))
      | ~ r2_hidden(A_145,a_2_0_orders_2('#skF_5',k1_tarski('#skF_6'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_1114])).

tff(c_1192,plain,(
    ! [E_144] :
      ( r2_orders_2('#skF_5',E_144,'#skF_7')
      | ~ r2_hidden(E_144,k1_tarski('#skF_6'))
      | ~ m1_subset_1(E_144,u1_struct_0('#skF_5'))
      | ~ r2_hidden('#skF_7',a_2_0_orders_2('#skF_5',k1_tarski('#skF_6'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_408,c_1186])).

tff(c_1199,plain,(
    ! [E_146] :
      ( r2_orders_2('#skF_5',E_146,'#skF_7')
      | ~ r2_hidden(E_146,k1_tarski('#skF_6'))
      | ~ m1_subset_1(E_146,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_306,c_1192])).

tff(c_1218,plain,
    ( r2_orders_2('#skF_5','#skF_6','#skF_7')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_6,c_1199])).

tff(c_1227,plain,(
    r2_orders_2('#skF_5','#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_1218])).

tff(c_1229,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_65,c_1227])).

tff(c_1230,plain,(
    ~ r2_hidden('#skF_7',k1_orders_2('#skF_5',k6_domain_1(u1_struct_0('#skF_5'),'#skF_6'))) ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_1295,plain,(
    ~ r2_hidden('#skF_7',k1_orders_2('#skF_5',k1_tarski('#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1294,c_1230])).

tff(c_1553,plain,(
    ~ r2_hidden('#skF_7',a_2_0_orders_2('#skF_5',k1_tarski('#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1546,c_1295])).

tff(c_1231,plain,(
    r2_orders_2('#skF_5','#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_1993,plain,(
    ! [D_235,B_236,C_237] :
      ( r2_hidden('#skF_4'(D_235,B_236,C_237,D_235),C_237)
      | r2_hidden(D_235,a_2_0_orders_2(B_236,C_237))
      | ~ m1_subset_1(D_235,u1_struct_0(B_236))
      | ~ m1_subset_1(C_237,k1_zfmisc_1(u1_struct_0(B_236)))
      | ~ l1_orders_2(B_236)
      | ~ v5_orders_2(B_236)
      | ~ v4_orders_2(B_236)
      | ~ v3_orders_2(B_236)
      | v2_struct_0(B_236) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_2002,plain,(
    ! [D_235] :
      ( r2_hidden('#skF_4'(D_235,'#skF_5',k1_tarski('#skF_6'),D_235),k1_tarski('#skF_6'))
      | r2_hidden(D_235,a_2_0_orders_2('#skF_5',k1_tarski('#skF_6')))
      | ~ m1_subset_1(D_235,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | ~ v4_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_1322,c_1993])).

tff(c_2017,plain,(
    ! [D_235] :
      ( r2_hidden('#skF_4'(D_235,'#skF_5',k1_tarski('#skF_6'),D_235),k1_tarski('#skF_6'))
      | r2_hidden(D_235,a_2_0_orders_2('#skF_5',k1_tarski('#skF_6')))
      | ~ m1_subset_1(D_235,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_2002])).

tff(c_2198,plain,(
    ! [D_249] :
      ( r2_hidden('#skF_4'(D_249,'#skF_5',k1_tarski('#skF_6'),D_249),k1_tarski('#skF_6'))
      | r2_hidden(D_249,a_2_0_orders_2('#skF_5',k1_tarski('#skF_6')))
      | ~ m1_subset_1(D_249,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_2017])).

tff(c_4,plain,(
    ! [C_8,A_4] :
      ( C_8 = A_4
      | ~ r2_hidden(C_8,k1_tarski(A_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2211,plain,(
    ! [D_250] :
      ( '#skF_4'(D_250,'#skF_5',k1_tarski('#skF_6'),D_250) = '#skF_6'
      | r2_hidden(D_250,a_2_0_orders_2('#skF_5',k1_tarski('#skF_6')))
      | ~ m1_subset_1(D_250,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_2198,c_4])).

tff(c_2225,plain,
    ( '#skF_4'('#skF_7','#skF_5',k1_tarski('#skF_6'),'#skF_7') = '#skF_6'
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_2211,c_1553])).

tff(c_2245,plain,(
    '#skF_4'('#skF_7','#skF_5',k1_tarski('#skF_6'),'#skF_7') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_2225])).

tff(c_2313,plain,(
    ! [B_252,D_253,C_254] :
      ( ~ r2_orders_2(B_252,'#skF_4'(D_253,B_252,C_254,D_253),D_253)
      | r2_hidden(D_253,a_2_0_orders_2(B_252,C_254))
      | ~ m1_subset_1(D_253,u1_struct_0(B_252))
      | ~ m1_subset_1(C_254,k1_zfmisc_1(u1_struct_0(B_252)))
      | ~ l1_orders_2(B_252)
      | ~ v5_orders_2(B_252)
      | ~ v4_orders_2(B_252)
      | ~ v3_orders_2(B_252)
      | v2_struct_0(B_252) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_2315,plain,
    ( ~ r2_orders_2('#skF_5','#skF_6','#skF_7')
    | r2_hidden('#skF_7',a_2_0_orders_2('#skF_5',k1_tarski('#skF_6')))
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | ~ m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_2245,c_2313])).

tff(c_2325,plain,
    ( r2_hidden('#skF_7',a_2_0_orders_2('#skF_5',k1_tarski('#skF_6')))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_1322,c_42,c_1231,c_2315])).

tff(c_2327,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_1553,c_2325])).

%------------------------------------------------------------------------------
