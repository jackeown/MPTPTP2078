%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1144+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:29 EST 2020

% Result     : Theorem 35.02s
% Output     : CNFRefutation 35.28s
% Verified   : 
% Statistics : Number of formulae       :  449 (10129 expanded)
%              Number of leaves         :   44 (3191 expanded)
%              Depth                    :   25
%              Number of atoms          :  905 (36588 expanded)
%              Number of equality atoms :  112 (3475 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_orders_2 > r1_orders_2 > v6_orders_2 > r7_relat_2 > r2_hidden > m1_subset_1 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > v1_relat_1 > l1_struct_0 > l1_orders_2 > k7_domain_1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > u1_struct_0 > u1_orders_2 > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(r3_orders_2,type,(
    r3_orders_2: ( $i * $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k7_domain_1,type,(
    k7_domain_1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff(r7_relat_2,type,(
    r7_relat_2: ( $i * $i ) > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v6_orders_2,type,(
    v6_orders_2: ( $i * $i ) > $o )).

tff(u1_orders_2,type,(
    u1_orders_2: $i > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_167,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ( ( v6_orders_2(k7_domain_1(u1_struct_0(A),B,C),A)
                    & m1_subset_1(k7_domain_1(u1_struct_0(A),B,C),k1_zfmisc_1(u1_struct_0(A))) )
                <=> ( r3_orders_2(A,B,C)
                    | r3_orders_2(A,C,B) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_orders_2)).

tff(f_90,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A)
        & m1_subset_1(C,A) )
     => m1_subset_1(k7_domain_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_domain_1)).

tff(f_126,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => ( r3_orders_2(A,B,C)
      <=> r1_orders_2(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

tff(f_139,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => r3_orders_2(A,B,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r3_orders_2)).

tff(f_94,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => m1_subset_1(u1_orders_2(A),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_orders_2)).

tff(f_28,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_65,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r7_relat_2(A,B)
        <=> ! [C,D] :
              ~ ( r2_hidden(C,B)
                & r2_hidden(D,B)
                & ~ r2_hidden(k4_tarski(C,D),A)
                & ~ r2_hidden(k4_tarski(D,C),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_relat_2)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(f_111,axiom,(
    ! [A,B,C] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A)
        & m1_subset_1(C,A) )
     => k7_domain_1(A,B,C) = k2_tarski(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_domain_1)).

tff(f_102,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_39,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v6_orders_2(B,A)
          <=> r7_relat_2(u1_orders_2(A),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_orders_2)).

tff(f_145,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_77,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r1_orders_2(A,B,C)
              <=> r2_hidden(k4_tarski(B,C),u1_orders_2(A)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_orders_2)).

tff(f_30,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(c_64,plain,(
    l1_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_44,plain,(
    ! [A_42] :
      ( l1_struct_0(A_42)
      | ~ l1_orders_2(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_68,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_62,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_60,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_130500,plain,(
    ! [A_90139,B_90140,C_90141] :
      ( m1_subset_1(k7_domain_1(A_90139,B_90140,C_90141),k1_zfmisc_1(A_90139))
      | ~ m1_subset_1(C_90141,A_90139)
      | ~ m1_subset_1(B_90140,A_90139)
      | v1_xboole_0(A_90139) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_66,plain,(
    v3_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_84,plain,
    ( v6_orders_2(k7_domain_1(u1_struct_0('#skF_5'),'#skF_6','#skF_7'),'#skF_5')
    | r3_orders_2('#skF_5','#skF_7','#skF_6')
    | r3_orders_2('#skF_5','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_137,plain,(
    r3_orders_2('#skF_5','#skF_6','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_84])).

tff(c_61435,plain,(
    ! [A_47514,B_47515,C_47516] :
      ( r1_orders_2(A_47514,B_47515,C_47516)
      | ~ r3_orders_2(A_47514,B_47515,C_47516)
      | ~ m1_subset_1(C_47516,u1_struct_0(A_47514))
      | ~ m1_subset_1(B_47515,u1_struct_0(A_47514))
      | ~ l1_orders_2(A_47514)
      | ~ v3_orders_2(A_47514)
      | v2_struct_0(A_47514) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_61451,plain,
    ( r1_orders_2('#skF_5','#skF_6','#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_137,c_61435])).

tff(c_61482,plain,
    ( r1_orders_2('#skF_5','#skF_6','#skF_7')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_60,c_61451])).

tff(c_61483,plain,(
    r1_orders_2('#skF_5','#skF_6','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_61482])).

tff(c_55535,plain,(
    ! [A_41514,B_41515,C_41516] :
      ( r3_orders_2(A_41514,B_41515,B_41515)
      | ~ m1_subset_1(C_41516,u1_struct_0(A_41514))
      | ~ m1_subset_1(B_41515,u1_struct_0(A_41514))
      | ~ l1_orders_2(A_41514)
      | ~ v3_orders_2(A_41514)
      | v2_struct_0(A_41514) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_55545,plain,(
    ! [B_41515] :
      ( r3_orders_2('#skF_5',B_41515,B_41515)
      | ~ m1_subset_1(B_41515,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_60,c_55535])).

tff(c_55566,plain,(
    ! [B_41515] :
      ( r3_orders_2('#skF_5',B_41515,B_41515)
      | ~ m1_subset_1(B_41515,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_55545])).

tff(c_55572,plain,(
    ! [B_41517] :
      ( r3_orders_2('#skF_5',B_41517,B_41517)
      | ~ m1_subset_1(B_41517,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_55566])).

tff(c_55590,plain,(
    r3_orders_2('#skF_5','#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_62,c_55572])).

tff(c_61447,plain,
    ( r1_orders_2('#skF_5','#skF_6','#skF_6')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_55590,c_61435])).

tff(c_61474,plain,
    ( r1_orders_2('#skF_5','#skF_6','#skF_6')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_61447])).

tff(c_61475,plain,(
    r1_orders_2('#skF_5','#skF_6','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_61474])).

tff(c_198,plain,(
    ! [A_85] :
      ( m1_subset_1(u1_orders_2(A_85),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_85),u1_struct_0(A_85))))
      | ~ l1_orders_2(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_2,plain,(
    ! [C_3,A_1,B_2] :
      ( v1_relat_1(C_3)
      | ~ m1_subset_1(C_3,k1_zfmisc_1(k2_zfmisc_1(A_1,B_2))) ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_205,plain,(
    ! [A_85] :
      ( v1_relat_1(u1_orders_2(A_85))
      | ~ l1_orders_2(A_85) ) ),
    inference(resolution,[status(thm)],[c_198,c_2])).

tff(c_175,plain,(
    ! [A_81,B_82] :
      ( r2_hidden('#skF_4'(A_81,B_82),B_82)
      | r7_relat_2(A_81,B_82)
      | ~ v1_relat_1(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_10,plain,(
    ! [D_14,B_10,A_9] :
      ( D_14 = B_10
      | D_14 = A_9
      | ~ r2_hidden(D_14,k2_tarski(A_9,B_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_67250,plain,(
    ! [A_52093,A_52094,B_52095] :
      ( '#skF_4'(A_52093,k2_tarski(A_52094,B_52095)) = B_52095
      | '#skF_4'(A_52093,k2_tarski(A_52094,B_52095)) = A_52094
      | r7_relat_2(A_52093,k2_tarski(A_52094,B_52095))
      | ~ v1_relat_1(A_52093) ) ),
    inference(resolution,[status(thm)],[c_175,c_10])).

tff(c_212,plain,(
    ! [A_97,B_98,C_99] :
      ( k7_domain_1(A_97,B_98,C_99) = k2_tarski(B_98,C_99)
      | ~ m1_subset_1(C_99,A_97)
      | ~ m1_subset_1(B_98,A_97)
      | v1_xboole_0(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_223,plain,(
    ! [B_98] :
      ( k7_domain_1(u1_struct_0('#skF_5'),B_98,'#skF_7') = k2_tarski(B_98,'#skF_7')
      | ~ m1_subset_1(B_98,u1_struct_0('#skF_5'))
      | v1_xboole_0(u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_60,c_212])).

tff(c_252,plain,(
    v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_223])).

tff(c_48,plain,(
    ! [A_44] :
      ( ~ v1_xboole_0(u1_struct_0(A_44))
      | ~ l1_struct_0(A_44)
      | v2_struct_0(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_255,plain,
    ( ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_252,c_48])).

tff(c_258,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_255])).

tff(c_262,plain,(
    ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_44,c_258])).

tff(c_266,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_262])).

tff(c_269,plain,(
    ! [B_112] :
      ( k7_domain_1(u1_struct_0('#skF_5'),B_112,'#skF_7') = k2_tarski(B_112,'#skF_7')
      | ~ m1_subset_1(B_112,u1_struct_0('#skF_5')) ) ),
    inference(splitRight,[status(thm)],[c_223])).

tff(c_277,plain,(
    k7_domain_1(u1_struct_0('#skF_5'),'#skF_6','#skF_7') = k2_tarski('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_62,c_269])).

tff(c_72,plain,
    ( ~ r3_orders_2('#skF_5','#skF_6','#skF_7')
    | ~ m1_subset_1(k7_domain_1(u1_struct_0('#skF_5'),'#skF_6','#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ v6_orders_2(k7_domain_1(u1_struct_0('#skF_5'),'#skF_6','#skF_7'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_227,plain,
    ( ~ m1_subset_1(k7_domain_1(u1_struct_0('#skF_5'),'#skF_6','#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ v6_orders_2(k7_domain_1(u1_struct_0('#skF_5'),'#skF_6','#skF_7'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_72])).

tff(c_228,plain,(
    ~ v6_orders_2(k7_domain_1(u1_struct_0('#skF_5'),'#skF_6','#skF_7'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_227])).

tff(c_304,plain,(
    ~ v6_orders_2(k2_tarski('#skF_6','#skF_7'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_277,c_228])).

tff(c_268,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_223])).

tff(c_42,plain,(
    ! [A_39,B_40,C_41] :
      ( m1_subset_1(k7_domain_1(A_39,B_40,C_41),k1_zfmisc_1(A_39))
      | ~ m1_subset_1(C_41,A_39)
      | ~ m1_subset_1(B_40,A_39)
      | v1_xboole_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_308,plain,
    ( m1_subset_1(k2_tarski('#skF_6','#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_277,c_42])).

tff(c_312,plain,
    ( m1_subset_1(k2_tarski('#skF_6','#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_308])).

tff(c_313,plain,(
    m1_subset_1(k2_tarski('#skF_6','#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_268,c_312])).

tff(c_6,plain,(
    ! [B_8,A_6] :
      ( v6_orders_2(B_8,A_6)
      | ~ r7_relat_2(u1_orders_2(A_6),B_8)
      | ~ m1_subset_1(B_8,k1_zfmisc_1(u1_struct_0(A_6)))
      | ~ l1_orders_2(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_322,plain,
    ( v6_orders_2(k2_tarski('#skF_6','#skF_7'),'#skF_5')
    | ~ r7_relat_2(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7'))
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_313,c_6])).

tff(c_331,plain,
    ( v6_orders_2(k2_tarski('#skF_6','#skF_7'),'#skF_5')
    | ~ r7_relat_2(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_322])).

tff(c_332,plain,(
    ~ r7_relat_2(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_304,c_331])).

tff(c_67524,plain,
    ( '#skF_4'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')) = '#skF_7'
    | '#skF_4'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')) = '#skF_6'
    | ~ v1_relat_1(u1_orders_2('#skF_5')) ),
    inference(resolution,[status(thm)],[c_67250,c_332])).

tff(c_67525,plain,(
    ~ v1_relat_1(u1_orders_2('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_67524])).

tff(c_67528,plain,(
    ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_205,c_67525])).

tff(c_67532,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_67528])).

tff(c_67534,plain,(
    v1_relat_1(u1_orders_2('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_67524])).

tff(c_186,plain,(
    ! [A_83,B_84] :
      ( r2_hidden('#skF_3'(A_83,B_84),B_84)
      | r7_relat_2(A_83,B_84)
      | ~ v1_relat_1(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_105495,plain,(
    ! [A_74551,A_74552,B_74553] :
      ( '#skF_3'(A_74551,k2_tarski(A_74552,B_74553)) = B_74553
      | '#skF_3'(A_74551,k2_tarski(A_74552,B_74553)) = A_74552
      | r7_relat_2(A_74551,k2_tarski(A_74552,B_74553))
      | ~ v1_relat_1(A_74551) ) ),
    inference(resolution,[status(thm)],[c_186,c_10])).

tff(c_105498,plain,
    ( '#skF_3'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')) = '#skF_7'
    | '#skF_3'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')) = '#skF_6'
    | ~ v1_relat_1(u1_orders_2('#skF_5')) ),
    inference(resolution,[status(thm)],[c_105495,c_332])).

tff(c_105837,plain,
    ( '#skF_3'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')) = '#skF_7'
    | '#skF_3'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_67534,c_105498])).

tff(c_105838,plain,(
    '#skF_3'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')) = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_105837])).

tff(c_36,plain,(
    ! [A_15,B_25] :
      ( r2_hidden('#skF_3'(A_15,B_25),B_25)
      | r7_relat_2(A_15,B_25)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_58,plain,(
    ! [A_54,C_56,B_55] :
      ( m1_subset_1(A_54,C_56)
      | ~ m1_subset_1(B_55,k1_zfmisc_1(C_56))
      | ~ r2_hidden(A_54,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_335,plain,(
    ! [A_116] :
      ( m1_subset_1(A_116,u1_struct_0('#skF_5'))
      | ~ r2_hidden(A_116,k2_tarski('#skF_6','#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_313,c_58])).

tff(c_352,plain,(
    ! [A_15] :
      ( m1_subset_1('#skF_3'(A_15,k2_tarski('#skF_6','#skF_7')),u1_struct_0('#skF_5'))
      | r7_relat_2(A_15,k2_tarski('#skF_6','#skF_7'))
      | ~ v1_relat_1(A_15) ) ),
    inference(resolution,[status(thm)],[c_36,c_335])).

tff(c_40,plain,(
    ! [B_36,C_38,A_32] :
      ( r2_hidden(k4_tarski(B_36,C_38),u1_orders_2(A_32))
      | ~ r1_orders_2(A_32,B_36,C_38)
      | ~ m1_subset_1(C_38,u1_struct_0(A_32))
      | ~ m1_subset_1(B_36,u1_struct_0(A_32))
      | ~ l1_orders_2(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_62055,plain,(
    ! [A_47984,B_47985,C_47986] :
      ( r3_orders_2(A_47984,B_47985,C_47986)
      | ~ r1_orders_2(A_47984,B_47985,C_47986)
      | ~ m1_subset_1(C_47986,u1_struct_0(A_47984))
      | ~ m1_subset_1(B_47985,u1_struct_0(A_47984))
      | ~ l1_orders_2(A_47984)
      | ~ v3_orders_2(A_47984)
      | v2_struct_0(A_47984) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_62074,plain,(
    ! [B_47985] :
      ( r3_orders_2('#skF_5',B_47985,'#skF_6')
      | ~ r1_orders_2('#skF_5',B_47985,'#skF_6')
      | ~ m1_subset_1(B_47985,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_62,c_62055])).

tff(c_62105,plain,(
    ! [B_47985] :
      ( r3_orders_2('#skF_5',B_47985,'#skF_6')
      | ~ r1_orders_2('#skF_5',B_47985,'#skF_6')
      | ~ m1_subset_1(B_47985,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62074])).

tff(c_62144,plain,(
    ! [B_48120] :
      ( r3_orders_2('#skF_5',B_48120,'#skF_6')
      | ~ r1_orders_2('#skF_5',B_48120,'#skF_6')
      | ~ m1_subset_1(B_48120,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_62105])).

tff(c_62175,plain,
    ( r3_orders_2('#skF_5','#skF_7','#skF_6')
    | ~ r1_orders_2('#skF_5','#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_60,c_62144])).

tff(c_62179,plain,(
    ~ r1_orders_2('#skF_5','#skF_7','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_62175])).

tff(c_87753,plain,(
    ! [A_65015,A_65016,B_65017] :
      ( '#skF_3'(A_65015,k2_tarski(A_65016,B_65017)) = B_65017
      | '#skF_3'(A_65015,k2_tarski(A_65016,B_65017)) = A_65016
      | r7_relat_2(A_65015,k2_tarski(A_65016,B_65017))
      | ~ v1_relat_1(A_65015) ) ),
    inference(resolution,[status(thm)],[c_186,c_10])).

tff(c_87756,plain,
    ( '#skF_3'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')) = '#skF_7'
    | '#skF_3'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')) = '#skF_6'
    | ~ v1_relat_1(u1_orders_2('#skF_5')) ),
    inference(resolution,[status(thm)],[c_87753,c_332])).

tff(c_88095,plain,
    ( '#skF_3'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')) = '#skF_7'
    | '#skF_3'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_67534,c_87756])).

tff(c_88096,plain,(
    '#skF_3'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')) = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_88095])).

tff(c_67533,plain,
    ( '#skF_4'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')) = '#skF_6'
    | '#skF_4'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')) = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_67524])).

tff(c_67742,plain,(
    '#skF_4'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')) = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_67533])).

tff(c_32,plain,(
    ! [A_15,B_25] :
      ( ~ r2_hidden(k4_tarski('#skF_3'(A_15,B_25),'#skF_4'(A_15,B_25)),A_15)
      | r7_relat_2(A_15,B_25)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_67758,plain,
    ( ~ r2_hidden(k4_tarski('#skF_3'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')),'#skF_7'),u1_orders_2('#skF_5'))
    | r7_relat_2(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7'))
    | ~ v1_relat_1(u1_orders_2('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_67742,c_32])).

tff(c_67904,plain,
    ( ~ r2_hidden(k4_tarski('#skF_3'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')),'#skF_7'),u1_orders_2('#skF_5'))
    | r7_relat_2(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_67534,c_67758])).

tff(c_67905,plain,(
    ~ r2_hidden(k4_tarski('#skF_3'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')),'#skF_7'),u1_orders_2('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_332,c_67904])).

tff(c_67921,plain,
    ( ~ r1_orders_2('#skF_5','#skF_3'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')),'#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_3'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')),u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_67905])).

tff(c_67939,plain,
    ( ~ r1_orders_2('#skF_5','#skF_3'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')),'#skF_7')
    | ~ m1_subset_1('#skF_3'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')),u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_60,c_67921])).

tff(c_72983,plain,(
    ~ m1_subset_1('#skF_3'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')),u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_67939])).

tff(c_73033,plain,
    ( r7_relat_2(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7'))
    | ~ v1_relat_1(u1_orders_2('#skF_5')) ),
    inference(resolution,[status(thm)],[c_352,c_72983])).

tff(c_73044,plain,(
    r7_relat_2(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_67534,c_73033])).

tff(c_73046,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_332,c_73044])).

tff(c_73047,plain,(
    ~ r1_orders_2('#skF_5','#skF_3'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_67939])).

tff(c_88475,plain,(
    ~ r1_orders_2('#skF_5','#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88096,c_73047])).

tff(c_88490,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_61483,c_88475])).

tff(c_88491,plain,(
    '#skF_3'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')) = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_88095])).

tff(c_55589,plain,(
    r3_orders_2('#skF_5','#skF_7','#skF_7') ),
    inference(resolution,[status(thm)],[c_60,c_55572])).

tff(c_61449,plain,
    ( r1_orders_2('#skF_5','#skF_7','#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_55589,c_61435])).

tff(c_61478,plain,
    ( r1_orders_2('#skF_5','#skF_7','#skF_7')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_60,c_61449])).

tff(c_61479,plain,(
    r1_orders_2('#skF_5','#skF_7','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_61478])).

tff(c_81411,plain,(
    ! [A_60186,A_60187,B_60188] :
      ( '#skF_3'(A_60186,k2_tarski(A_60187,B_60188)) = B_60188
      | '#skF_3'(A_60186,k2_tarski(A_60187,B_60188)) = A_60187
      | r7_relat_2(A_60186,k2_tarski(A_60187,B_60188))
      | ~ v1_relat_1(A_60186) ) ),
    inference(resolution,[status(thm)],[c_186,c_10])).

tff(c_81414,plain,
    ( '#skF_3'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')) = '#skF_7'
    | '#skF_3'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')) = '#skF_6'
    | ~ v1_relat_1(u1_orders_2('#skF_5')) ),
    inference(resolution,[status(thm)],[c_81411,c_332])).

tff(c_81753,plain,
    ( '#skF_3'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')) = '#skF_7'
    | '#skF_3'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_67534,c_81414])).

tff(c_81754,plain,(
    '#skF_3'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')) = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_81753])).

tff(c_73048,plain,(
    m1_subset_1('#skF_3'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')),u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_67939])).

tff(c_62106,plain,(
    ! [B_47985] :
      ( r3_orders_2('#skF_5',B_47985,'#skF_6')
      | ~ r1_orders_2('#skF_5',B_47985,'#skF_6')
      | ~ m1_subset_1(B_47985,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_62105])).

tff(c_73312,plain,
    ( r3_orders_2('#skF_5','#skF_3'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')),'#skF_6')
    | ~ r1_orders_2('#skF_5','#skF_3'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')),'#skF_6') ),
    inference(resolution,[status(thm)],[c_73048,c_62106])).

tff(c_75390,plain,(
    ~ r1_orders_2('#skF_5','#skF_3'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_73312])).

tff(c_81761,plain,(
    ~ r1_orders_2('#skF_5','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_81754,c_75390])).

tff(c_81776,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_61475,c_81761])).

tff(c_81777,plain,(
    '#skF_3'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')) = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_81753])).

tff(c_30,plain,(
    ! [A_15,B_25] :
      ( ~ r2_hidden(k4_tarski('#skF_4'(A_15,B_25),'#skF_3'(A_15,B_25)),A_15)
      | r7_relat_2(A_15,B_25)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_67761,plain,
    ( ~ r2_hidden(k4_tarski('#skF_7','#skF_3'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7'))),u1_orders_2('#skF_5'))
    | r7_relat_2(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7'))
    | ~ v1_relat_1(u1_orders_2('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_67742,c_30])).

tff(c_67907,plain,
    ( ~ r2_hidden(k4_tarski('#skF_7','#skF_3'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7'))),u1_orders_2('#skF_5'))
    | r7_relat_2(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_67534,c_67761])).

tff(c_67908,plain,(
    ~ r2_hidden(k4_tarski('#skF_7','#skF_3'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7'))),u1_orders_2('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_332,c_67907])).

tff(c_67948,plain,
    ( ~ r1_orders_2('#skF_5','#skF_7','#skF_3'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')))
    | ~ m1_subset_1('#skF_3'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')),u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_67908])).

tff(c_67966,plain,
    ( ~ r1_orders_2('#skF_5','#skF_7','#skF_3'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')))
    | ~ m1_subset_1('#skF_3'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')),u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_60,c_67948])).

tff(c_73880,plain,(
    ~ r1_orders_2('#skF_5','#skF_7','#skF_3'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73048,c_67966])).

tff(c_81809,plain,(
    ~ r1_orders_2('#skF_5','#skF_7','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_81777,c_73880])).

tff(c_81822,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_61479,c_81809])).

tff(c_81824,plain,(
    r1_orders_2('#skF_5','#skF_3'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_73312])).

tff(c_88499,plain,(
    r1_orders_2('#skF_5','#skF_7','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88491,c_81824])).

tff(c_88513,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62179,c_88499])).

tff(c_88514,plain,(
    '#skF_4'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')) = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_67533])).

tff(c_88534,plain,
    ( ~ r2_hidden(k4_tarski('#skF_6','#skF_3'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7'))),u1_orders_2('#skF_5'))
    | r7_relat_2(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7'))
    | ~ v1_relat_1(u1_orders_2('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_88514,c_30])).

tff(c_88680,plain,
    ( ~ r2_hidden(k4_tarski('#skF_6','#skF_3'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7'))),u1_orders_2('#skF_5'))
    | r7_relat_2(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_67534,c_88534])).

tff(c_88681,plain,(
    ~ r2_hidden(k4_tarski('#skF_6','#skF_3'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7'))),u1_orders_2('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_332,c_88680])).

tff(c_88722,plain,
    ( ~ r1_orders_2('#skF_5','#skF_6','#skF_3'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')))
    | ~ m1_subset_1('#skF_3'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')),u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_88681])).

tff(c_88740,plain,
    ( ~ r1_orders_2('#skF_5','#skF_6','#skF_3'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')))
    | ~ m1_subset_1('#skF_3'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')),u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_88722])).

tff(c_93679,plain,(
    ~ m1_subset_1('#skF_3'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')),u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_88740])).

tff(c_93729,plain,
    ( r7_relat_2(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7'))
    | ~ v1_relat_1(u1_orders_2('#skF_5')) ),
    inference(resolution,[status(thm)],[c_352,c_93679])).

tff(c_93740,plain,(
    r7_relat_2(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_67534,c_93729])).

tff(c_93742,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_332,c_93740])).

tff(c_93744,plain,(
    m1_subset_1('#skF_3'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')),u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_88740])).

tff(c_88531,plain,
    ( ~ r2_hidden(k4_tarski('#skF_3'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')),'#skF_6'),u1_orders_2('#skF_5'))
    | r7_relat_2(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7'))
    | ~ v1_relat_1(u1_orders_2('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_88514,c_32])).

tff(c_88677,plain,
    ( ~ r2_hidden(k4_tarski('#skF_3'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')),'#skF_6'),u1_orders_2('#skF_5'))
    | r7_relat_2(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_67534,c_88531])).

tff(c_88678,plain,(
    ~ r2_hidden(k4_tarski('#skF_3'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')),'#skF_6'),u1_orders_2('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_332,c_88677])).

tff(c_88695,plain,
    ( ~ r1_orders_2('#skF_5','#skF_3'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')),'#skF_6')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_3'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')),u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_88678])).

tff(c_88713,plain,
    ( ~ r1_orders_2('#skF_5','#skF_3'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')),'#skF_6')
    | ~ m1_subset_1('#skF_3'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')),u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_88695])).

tff(c_94472,plain,(
    ~ r1_orders_2('#skF_5','#skF_3'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_93744,c_88713])).

tff(c_105847,plain,(
    ~ r1_orders_2('#skF_5','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_105838,c_94472])).

tff(c_105863,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_61475,c_105847])).

tff(c_105864,plain,(
    '#skF_3'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')) = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_105837])).

tff(c_93743,plain,(
    ~ r1_orders_2('#skF_5','#skF_6','#skF_3'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7'))) ),
    inference(splitRight,[status(thm)],[c_88740])).

tff(c_105877,plain,(
    ~ r1_orders_2('#skF_5','#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_105864,c_93743])).

tff(c_105891,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_61483,c_105877])).

tff(c_105893,plain,(
    r1_orders_2('#skF_5','#skF_7','#skF_6') ),
    inference(splitRight,[status(thm)],[c_62175])).

tff(c_119895,plain,(
    ! [A_83941,A_83942,B_83943] :
      ( '#skF_3'(A_83941,k2_tarski(A_83942,B_83943)) = B_83943
      | '#skF_3'(A_83941,k2_tarski(A_83942,B_83943)) = A_83942
      | r7_relat_2(A_83941,k2_tarski(A_83942,B_83943))
      | ~ v1_relat_1(A_83941) ) ),
    inference(resolution,[status(thm)],[c_186,c_10])).

tff(c_120235,plain,
    ( '#skF_3'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')) = '#skF_7'
    | '#skF_3'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')) = '#skF_6'
    | ~ v1_relat_1(u1_orders_2('#skF_5')) ),
    inference(resolution,[status(thm)],[c_119895,c_332])).

tff(c_120236,plain,(
    ~ v1_relat_1(u1_orders_2('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_120235])).

tff(c_120239,plain,(
    ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_205,c_120236])).

tff(c_120243,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_120239])).

tff(c_120245,plain,(
    v1_relat_1(u1_orders_2('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_120235])).

tff(c_130098,plain,(
    ! [A_90026,A_90027,B_90028] :
      ( '#skF_4'(A_90026,k2_tarski(A_90027,B_90028)) = B_90028
      | '#skF_4'(A_90026,k2_tarski(A_90027,B_90028)) = A_90027
      | r7_relat_2(A_90026,k2_tarski(A_90027,B_90028))
      | ~ v1_relat_1(A_90026) ) ),
    inference(resolution,[status(thm)],[c_175,c_10])).

tff(c_130101,plain,
    ( '#skF_4'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')) = '#skF_7'
    | '#skF_4'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')) = '#skF_6'
    | ~ v1_relat_1(u1_orders_2('#skF_5')) ),
    inference(resolution,[status(thm)],[c_130098,c_332])).

tff(c_130440,plain,
    ( '#skF_4'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')) = '#skF_7'
    | '#skF_4'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_120245,c_130101])).

tff(c_130441,plain,(
    '#skF_4'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')) = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_130440])).

tff(c_34,plain,(
    ! [A_15,B_25] :
      ( r2_hidden('#skF_4'(A_15,B_25),B_25)
      | r7_relat_2(A_15,B_25)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_353,plain,(
    ! [A_15] :
      ( m1_subset_1('#skF_4'(A_15,k2_tarski('#skF_6','#skF_7')),u1_struct_0('#skF_5'))
      | r7_relat_2(A_15,k2_tarski('#skF_6','#skF_7'))
      | ~ v1_relat_1(A_15) ) ),
    inference(resolution,[status(thm)],[c_34,c_335])).

tff(c_124737,plain,(
    ! [A_86926,A_86927,B_86928] :
      ( '#skF_4'(A_86926,k2_tarski(A_86927,B_86928)) = B_86928
      | '#skF_4'(A_86926,k2_tarski(A_86927,B_86928)) = A_86927
      | r7_relat_2(A_86926,k2_tarski(A_86927,B_86928))
      | ~ v1_relat_1(A_86926) ) ),
    inference(resolution,[status(thm)],[c_175,c_10])).

tff(c_124740,plain,
    ( '#skF_4'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')) = '#skF_7'
    | '#skF_4'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')) = '#skF_6'
    | ~ v1_relat_1(u1_orders_2('#skF_5')) ),
    inference(resolution,[status(thm)],[c_124737,c_332])).

tff(c_125079,plain,
    ( '#skF_4'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')) = '#skF_7'
    | '#skF_4'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_120245,c_124740])).

tff(c_125080,plain,(
    '#skF_4'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')) = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_125079])).

tff(c_120244,plain,
    ( '#skF_3'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')) = '#skF_6'
    | '#skF_3'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')) = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_120235])).

tff(c_120367,plain,(
    '#skF_3'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')) = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_120244])).

tff(c_120383,plain,
    ( ~ r2_hidden(k4_tarski('#skF_7','#skF_4'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7'))),u1_orders_2('#skF_5'))
    | r7_relat_2(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7'))
    | ~ v1_relat_1(u1_orders_2('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_120367,c_32])).

tff(c_120565,plain,
    ( ~ r2_hidden(k4_tarski('#skF_7','#skF_4'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7'))),u1_orders_2('#skF_5'))
    | r7_relat_2(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_120245,c_120383])).

tff(c_120566,plain,(
    ~ r2_hidden(k4_tarski('#skF_7','#skF_4'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7'))),u1_orders_2('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_332,c_120565])).

tff(c_120588,plain,
    ( ~ r1_orders_2('#skF_5','#skF_7','#skF_4'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')))
    | ~ m1_subset_1('#skF_4'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')),u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_120566])).

tff(c_120606,plain,
    ( ~ r1_orders_2('#skF_5','#skF_7','#skF_4'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')))
    | ~ m1_subset_1('#skF_4'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')),u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_60,c_120588])).

tff(c_120640,plain,(
    ~ m1_subset_1('#skF_4'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')),u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_120606])).

tff(c_120689,plain,
    ( r7_relat_2(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7'))
    | ~ v1_relat_1(u1_orders_2('#skF_5')) ),
    inference(resolution,[status(thm)],[c_353,c_120640])).

tff(c_120700,plain,(
    r7_relat_2(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_120245,c_120689])).

tff(c_120702,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_332,c_120700])).

tff(c_120704,plain,(
    m1_subset_1('#skF_4'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')),u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_120606])).

tff(c_120386,plain,
    ( ~ r2_hidden(k4_tarski('#skF_4'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')),'#skF_7'),u1_orders_2('#skF_5'))
    | r7_relat_2(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7'))
    | ~ v1_relat_1(u1_orders_2('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_120367,c_30])).

tff(c_120568,plain,
    ( ~ r2_hidden(k4_tarski('#skF_4'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')),'#skF_7'),u1_orders_2('#skF_5'))
    | r7_relat_2(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_120245,c_120386])).

tff(c_120569,plain,(
    ~ r2_hidden(k4_tarski('#skF_4'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')),'#skF_7'),u1_orders_2('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_332,c_120568])).

tff(c_120621,plain,
    ( ~ r1_orders_2('#skF_5','#skF_4'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')),'#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_4'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')),u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_120569])).

tff(c_120639,plain,
    ( ~ r1_orders_2('#skF_5','#skF_4'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')),'#skF_7')
    | ~ m1_subset_1('#skF_4'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')),u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_60,c_120621])).

tff(c_121946,plain,(
    ~ r1_orders_2('#skF_5','#skF_4'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_120704,c_120639])).

tff(c_125089,plain,(
    ~ r1_orders_2('#skF_5','#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_125080,c_121946])).

tff(c_125105,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_61483,c_125089])).

tff(c_125106,plain,(
    '#skF_4'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')) = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_125079])).

tff(c_125116,plain,(
    ~ r1_orders_2('#skF_5','#skF_7','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_125106,c_121946])).

tff(c_125131,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_61479,c_125116])).

tff(c_125132,plain,(
    '#skF_3'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')) = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_120244])).

tff(c_125508,plain,
    ( ~ r2_hidden(k4_tarski('#skF_6','#skF_4'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7'))),u1_orders_2('#skF_5'))
    | r7_relat_2(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7'))
    | ~ v1_relat_1(u1_orders_2('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_125132,c_32])).

tff(c_125690,plain,
    ( ~ r2_hidden(k4_tarski('#skF_6','#skF_4'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7'))),u1_orders_2('#skF_5'))
    | r7_relat_2(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_120245,c_125508])).

tff(c_125691,plain,(
    ~ r2_hidden(k4_tarski('#skF_6','#skF_4'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7'))),u1_orders_2('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_332,c_125690])).

tff(c_125714,plain,
    ( ~ r1_orders_2('#skF_5','#skF_6','#skF_4'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')))
    | ~ m1_subset_1('#skF_4'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')),u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_125691])).

tff(c_125732,plain,
    ( ~ r1_orders_2('#skF_5','#skF_6','#skF_4'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')))
    | ~ m1_subset_1('#skF_4'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')),u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_125714])).

tff(c_125766,plain,(
    ~ m1_subset_1('#skF_4'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')),u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_125732])).

tff(c_126158,plain,
    ( r7_relat_2(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7'))
    | ~ v1_relat_1(u1_orders_2('#skF_5')) ),
    inference(resolution,[status(thm)],[c_353,c_125766])).

tff(c_126169,plain,(
    r7_relat_2(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_120245,c_126158])).

tff(c_126171,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_332,c_126169])).

tff(c_126173,plain,(
    m1_subset_1('#skF_4'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')),u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_125732])).

tff(c_125511,plain,
    ( ~ r2_hidden(k4_tarski('#skF_4'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')),'#skF_6'),u1_orders_2('#skF_5'))
    | r7_relat_2(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7'))
    | ~ v1_relat_1(u1_orders_2('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_125132,c_30])).

tff(c_125693,plain,
    ( ~ r2_hidden(k4_tarski('#skF_4'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')),'#skF_6'),u1_orders_2('#skF_5'))
    | r7_relat_2(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_120245,c_125511])).

tff(c_125694,plain,(
    ~ r2_hidden(k4_tarski('#skF_4'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')),'#skF_6'),u1_orders_2('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_332,c_125693])).

tff(c_125747,plain,
    ( ~ r1_orders_2('#skF_5','#skF_4'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')),'#skF_6')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_4'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')),u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_125694])).

tff(c_125765,plain,
    ( ~ r1_orders_2('#skF_5','#skF_4'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')),'#skF_6')
    | ~ m1_subset_1('#skF_4'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')),u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_125747])).

tff(c_127423,plain,(
    ~ r1_orders_2('#skF_5','#skF_4'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_126173,c_125765])).

tff(c_130451,plain,(
    ~ r1_orders_2('#skF_5','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_130441,c_127423])).

tff(c_130467,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_61475,c_130451])).

tff(c_130468,plain,(
    '#skF_4'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')) = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_130440])).

tff(c_130479,plain,(
    ~ r1_orders_2('#skF_5','#skF_7','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_130468,c_127423])).

tff(c_130494,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_105893,c_130479])).

tff(c_130495,plain,(
    ~ m1_subset_1(k7_domain_1(u1_struct_0('#skF_5'),'#skF_6','#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_227])).

tff(c_130503,plain,
    ( ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_130500,c_130495])).

tff(c_130522,plain,(
    v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_130503])).

tff(c_130530,plain,
    ( ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_130522,c_48])).

tff(c_130533,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_130530])).

tff(c_130536,plain,(
    ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_44,c_130533])).

tff(c_130540,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_130536])).

tff(c_130542,plain,(
    ~ r3_orders_2('#skF_5','#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_317338,plain,(
    ! [A_232400,B_232401,C_232402] :
      ( r3_orders_2(A_232400,B_232401,C_232402)
      | ~ r1_orders_2(A_232400,B_232401,C_232402)
      | ~ m1_subset_1(C_232402,u1_struct_0(A_232400))
      | ~ m1_subset_1(B_232401,u1_struct_0(A_232400))
      | ~ l1_orders_2(A_232400)
      | ~ v3_orders_2(A_232400)
      | v2_struct_0(A_232400) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_317343,plain,(
    ! [B_232401] :
      ( r3_orders_2('#skF_5',B_232401,'#skF_7')
      | ~ r1_orders_2('#skF_5',B_232401,'#skF_7')
      | ~ m1_subset_1(B_232401,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_60,c_317338])).

tff(c_317348,plain,(
    ! [B_232401] :
      ( r3_orders_2('#skF_5',B_232401,'#skF_7')
      | ~ r1_orders_2('#skF_5',B_232401,'#skF_7')
      | ~ m1_subset_1(B_232401,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_317343])).

tff(c_317354,plain,(
    ! [B_232469] :
      ( r3_orders_2('#skF_5',B_232469,'#skF_7')
      | ~ r1_orders_2('#skF_5',B_232469,'#skF_7')
      | ~ m1_subset_1(B_232469,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_317348])).

tff(c_317360,plain,
    ( r3_orders_2('#skF_5','#skF_6','#skF_7')
    | ~ r1_orders_2('#skF_5','#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_62,c_317354])).

tff(c_317365,plain,(
    ~ r1_orders_2('#skF_5','#skF_6','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_130542,c_317360])).

tff(c_82,plain,
    ( m1_subset_1(k7_domain_1(u1_struct_0('#skF_5'),'#skF_6','#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | r3_orders_2('#skF_5','#skF_7','#skF_6')
    | r3_orders_2('#skF_5','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_130562,plain,
    ( m1_subset_1(k7_domain_1(u1_struct_0('#skF_5'),'#skF_6','#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | r3_orders_2('#skF_5','#skF_7','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_130542,c_82])).

tff(c_130563,plain,(
    r3_orders_2('#skF_5','#skF_7','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_130562])).

tff(c_209075,plain,(
    ! [A_150066,B_150067,C_150068] :
      ( r1_orders_2(A_150066,B_150067,C_150068)
      | ~ r3_orders_2(A_150066,B_150067,C_150068)
      | ~ m1_subset_1(C_150068,u1_struct_0(A_150066))
      | ~ m1_subset_1(B_150067,u1_struct_0(A_150066))
      | ~ l1_orders_2(A_150066)
      | ~ v3_orders_2(A_150066)
      | v2_struct_0(A_150066) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_209085,plain,
    ( r1_orders_2('#skF_5','#skF_7','#skF_6')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_130563,c_209075])).

tff(c_209104,plain,
    ( r1_orders_2('#skF_5','#skF_7','#skF_6')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_60,c_62,c_209085])).

tff(c_209105,plain,(
    r1_orders_2('#skF_5','#skF_7','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_209104])).

tff(c_209705,plain,(
    ! [A_150604,B_150605,C_150606] :
      ( r3_orders_2(A_150604,B_150605,C_150606)
      | ~ r1_orders_2(A_150604,B_150605,C_150606)
      | ~ m1_subset_1(C_150606,u1_struct_0(A_150604))
      | ~ m1_subset_1(B_150605,u1_struct_0(A_150604))
      | ~ l1_orders_2(A_150604)
      | ~ v3_orders_2(A_150604)
      | v2_struct_0(A_150604) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_209722,plain,(
    ! [B_150605] :
      ( r3_orders_2('#skF_5',B_150605,'#skF_7')
      | ~ r1_orders_2('#skF_5',B_150605,'#skF_7')
      | ~ m1_subset_1(B_150605,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_60,c_209705])).

tff(c_209751,plain,(
    ! [B_150605] :
      ( r3_orders_2('#skF_5',B_150605,'#skF_7')
      | ~ r1_orders_2('#skF_5',B_150605,'#skF_7')
      | ~ m1_subset_1(B_150605,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_209722])).

tff(c_209757,plain,(
    ! [B_150673] :
      ( r3_orders_2('#skF_5',B_150673,'#skF_7')
      | ~ r1_orders_2('#skF_5',B_150673,'#skF_7')
      | ~ m1_subset_1(B_150673,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_209751])).

tff(c_209781,plain,
    ( r3_orders_2('#skF_5','#skF_6','#skF_7')
    | ~ r1_orders_2('#skF_5','#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_62,c_209757])).

tff(c_209793,plain,(
    ~ r1_orders_2('#skF_5','#skF_6','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_130542,c_209781])).

tff(c_130604,plain,(
    ! [A_90159] :
      ( m1_subset_1(u1_orders_2(A_90159),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_90159),u1_struct_0(A_90159))))
      | ~ l1_orders_2(A_90159) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_130611,plain,(
    ! [A_90159] :
      ( v1_relat_1(u1_orders_2(A_90159))
      | ~ l1_orders_2(A_90159) ) ),
    inference(resolution,[status(thm)],[c_130604,c_2])).

tff(c_130593,plain,(
    ! [A_90157,B_90158] :
      ( r2_hidden('#skF_3'(A_90157,B_90158),B_90158)
      | r7_relat_2(A_90157,B_90158)
      | ~ v1_relat_1(A_90157) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_221097,plain,(
    ! [A_156960,A_156961,B_156962] :
      ( '#skF_3'(A_156960,k2_tarski(A_156961,B_156962)) = B_156962
      | '#skF_3'(A_156960,k2_tarski(A_156961,B_156962)) = A_156961
      | r7_relat_2(A_156960,k2_tarski(A_156961,B_156962))
      | ~ v1_relat_1(A_156960) ) ),
    inference(resolution,[status(thm)],[c_130593,c_10])).

tff(c_130620,plain,(
    ! [A_90174,B_90175,C_90176] :
      ( k7_domain_1(A_90174,B_90175,C_90176) = k2_tarski(B_90175,C_90176)
      | ~ m1_subset_1(C_90176,A_90174)
      | ~ m1_subset_1(B_90175,A_90174)
      | v1_xboole_0(A_90174) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_130632,plain,(
    ! [B_90175] :
      ( k7_domain_1(u1_struct_0('#skF_5'),B_90175,'#skF_6') = k2_tarski(B_90175,'#skF_6')
      | ~ m1_subset_1(B_90175,u1_struct_0('#skF_5'))
      | v1_xboole_0(u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_62,c_130620])).

tff(c_130659,plain,(
    v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_130632])).

tff(c_130662,plain,
    ( ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_130659,c_48])).

tff(c_130665,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_130662])).

tff(c_130668,plain,(
    ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_44,c_130665])).

tff(c_130672,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_130668])).

tff(c_130674,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_130632])).

tff(c_4,plain,(
    ! [B_5,A_4] : k2_tarski(B_5,A_4) = k2_tarski(A_4,B_5) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_130676,plain,(
    ! [B_90186] :
      ( k7_domain_1(u1_struct_0('#skF_5'),B_90186,'#skF_6') = k2_tarski(B_90186,'#skF_6')
      | ~ m1_subset_1(B_90186,u1_struct_0('#skF_5')) ) ),
    inference(splitRight,[status(thm)],[c_130632])).

tff(c_130679,plain,(
    k7_domain_1(u1_struct_0('#skF_5'),'#skF_7','#skF_6') = k2_tarski('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_60,c_130676])).

tff(c_130684,plain,(
    k7_domain_1(u1_struct_0('#skF_5'),'#skF_7','#skF_6') = k2_tarski('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_130679])).

tff(c_130689,plain,
    ( m1_subset_1(k2_tarski('#skF_6','#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_130684,c_42])).

tff(c_130693,plain,
    ( m1_subset_1(k2_tarski('#skF_6','#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_62,c_130689])).

tff(c_130694,plain,(
    m1_subset_1(k2_tarski('#skF_6','#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_130674,c_130693])).

tff(c_8,plain,(
    ! [A_6,B_8] :
      ( r7_relat_2(u1_orders_2(A_6),B_8)
      | ~ v6_orders_2(B_8,A_6)
      | ~ m1_subset_1(B_8,k1_zfmisc_1(u1_struct_0(A_6)))
      | ~ l1_orders_2(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_130700,plain,
    ( r7_relat_2(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7'))
    | ~ v6_orders_2(k2_tarski('#skF_6','#skF_7'),'#skF_5')
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_130694,c_8])).

tff(c_130709,plain,
    ( r7_relat_2(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7'))
    | ~ v6_orders_2(k2_tarski('#skF_6','#skF_7'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_130700])).

tff(c_130786,plain,(
    ~ v6_orders_2(k2_tarski('#skF_6','#skF_7'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_130709])).

tff(c_130703,plain,
    ( v6_orders_2(k2_tarski('#skF_6','#skF_7'),'#skF_5')
    | ~ r7_relat_2(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7'))
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_130694,c_6])).

tff(c_130712,plain,
    ( v6_orders_2(k2_tarski('#skF_6','#skF_7'),'#skF_5')
    | ~ r7_relat_2(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_130703])).

tff(c_179292,plain,(
    ~ r7_relat_2(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_130786,c_130712])).

tff(c_221377,plain,
    ( '#skF_3'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')) = '#skF_7'
    | '#skF_3'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')) = '#skF_6'
    | ~ v1_relat_1(u1_orders_2('#skF_5')) ),
    inference(resolution,[status(thm)],[c_221097,c_179292])).

tff(c_221378,plain,(
    ~ v1_relat_1(u1_orders_2('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_221377])).

tff(c_221381,plain,(
    ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_130611,c_221378])).

tff(c_221385,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_221381])).

tff(c_221387,plain,(
    v1_relat_1(u1_orders_2('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_221377])).

tff(c_130582,plain,(
    ! [A_90155,B_90156] :
      ( r2_hidden('#skF_4'(A_90155,B_90156),B_90156)
      | r7_relat_2(A_90155,B_90156)
      | ~ v1_relat_1(A_90155) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_242228,plain,(
    ! [A_173845,A_173846,B_173847] :
      ( '#skF_4'(A_173845,k2_tarski(A_173846,B_173847)) = B_173847
      | '#skF_4'(A_173845,k2_tarski(A_173846,B_173847)) = A_173846
      | r7_relat_2(A_173845,k2_tarski(A_173846,B_173847))
      | ~ v1_relat_1(A_173845) ) ),
    inference(resolution,[status(thm)],[c_130582,c_10])).

tff(c_242231,plain,
    ( '#skF_4'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')) = '#skF_7'
    | '#skF_4'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')) = '#skF_6'
    | ~ v1_relat_1(u1_orders_2('#skF_5')) ),
    inference(resolution,[status(thm)],[c_242228,c_179292])).

tff(c_242513,plain,
    ( '#skF_4'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')) = '#skF_7'
    | '#skF_4'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_221387,c_242231])).

tff(c_242514,plain,(
    '#skF_4'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')) = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_242513])).

tff(c_130787,plain,(
    ! [A_90189,B_90190,C_90191] :
      ( r3_orders_2(A_90189,B_90190,B_90190)
      | ~ m1_subset_1(C_90191,u1_struct_0(A_90189))
      | ~ m1_subset_1(B_90190,u1_struct_0(A_90189))
      | ~ l1_orders_2(A_90189)
      | ~ v3_orders_2(A_90189)
      | v2_struct_0(A_90189) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_130789,plain,(
    ! [B_90190] :
      ( r3_orders_2('#skF_5',B_90190,B_90190)
      | ~ m1_subset_1(B_90190,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_60,c_130787])).

tff(c_130794,plain,(
    ! [B_90190] :
      ( r3_orders_2('#skF_5',B_90190,B_90190)
      | ~ m1_subset_1(B_90190,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_130789])).

tff(c_130800,plain,(
    ! [B_90192] :
      ( r3_orders_2('#skF_5',B_90192,B_90192)
      | ~ m1_subset_1(B_90192,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_130794])).

tff(c_130805,plain,(
    r3_orders_2('#skF_5','#skF_7','#skF_7') ),
    inference(resolution,[status(thm)],[c_60,c_130800])).

tff(c_209083,plain,
    ( r1_orders_2('#skF_5','#skF_7','#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_130805,c_209075])).

tff(c_209100,plain,
    ( r1_orders_2('#skF_5','#skF_7','#skF_7')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_60,c_209083])).

tff(c_209101,plain,(
    r1_orders_2('#skF_5','#skF_7','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_209100])).

tff(c_130806,plain,(
    r3_orders_2('#skF_5','#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_62,c_130800])).

tff(c_209081,plain,
    ( r1_orders_2('#skF_5','#skF_6','#skF_6')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_130806,c_209075])).

tff(c_209096,plain,
    ( r1_orders_2('#skF_5','#skF_6','#skF_6')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_209081])).

tff(c_209097,plain,(
    r1_orders_2('#skF_5','#skF_6','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_209096])).

tff(c_240919,plain,(
    ! [A_173177,A_173178,B_173179] :
      ( '#skF_4'(A_173177,k2_tarski(A_173178,B_173179)) = B_173179
      | '#skF_4'(A_173177,k2_tarski(A_173178,B_173179)) = A_173178
      | r7_relat_2(A_173177,k2_tarski(A_173178,B_173179))
      | ~ v1_relat_1(A_173177) ) ),
    inference(resolution,[status(thm)],[c_130582,c_10])).

tff(c_240922,plain,
    ( '#skF_4'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')) = '#skF_7'
    | '#skF_4'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')) = '#skF_6'
    | ~ v1_relat_1(u1_orders_2('#skF_5')) ),
    inference(resolution,[status(thm)],[c_240919,c_179292])).

tff(c_241261,plain,
    ( '#skF_4'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')) = '#skF_7'
    | '#skF_4'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_221387,c_240922])).

tff(c_241262,plain,(
    '#skF_4'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')) = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_241261])).

tff(c_130740,plain,(
    ! [A_90187] :
      ( m1_subset_1(A_90187,u1_struct_0('#skF_5'))
      | ~ r2_hidden(A_90187,k2_tarski('#skF_6','#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_130694,c_58])).

tff(c_130758,plain,(
    ! [A_15] :
      ( m1_subset_1('#skF_4'(A_15,k2_tarski('#skF_6','#skF_7')),u1_struct_0('#skF_5'))
      | r7_relat_2(A_15,k2_tarski('#skF_6','#skF_7'))
      | ~ v1_relat_1(A_15) ) ),
    inference(resolution,[status(thm)],[c_34,c_130740])).

tff(c_233178,plain,(
    ! [A_167107,A_167108,B_167109] :
      ( '#skF_4'(A_167107,k2_tarski(A_167108,B_167109)) = B_167109
      | '#skF_4'(A_167107,k2_tarski(A_167108,B_167109)) = A_167108
      | r7_relat_2(A_167107,k2_tarski(A_167108,B_167109))
      | ~ v1_relat_1(A_167107) ) ),
    inference(resolution,[status(thm)],[c_130582,c_10])).

tff(c_233181,plain,
    ( '#skF_4'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')) = '#skF_7'
    | '#skF_4'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')) = '#skF_6'
    | ~ v1_relat_1(u1_orders_2('#skF_5')) ),
    inference(resolution,[status(thm)],[c_233178,c_179292])).

tff(c_233520,plain,
    ( '#skF_4'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')) = '#skF_7'
    | '#skF_4'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_221387,c_233181])).

tff(c_233521,plain,(
    '#skF_4'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')) = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_233520])).

tff(c_221386,plain,
    ( '#skF_3'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')) = '#skF_6'
    | '#skF_3'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')) = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_221377])).

tff(c_221495,plain,(
    '#skF_3'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')) = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_221386])).

tff(c_221505,plain,
    ( ~ r2_hidden(k4_tarski('#skF_4'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')),'#skF_7'),u1_orders_2('#skF_5'))
    | r7_relat_2(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7'))
    | ~ v1_relat_1(u1_orders_2('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_221495,c_30])).

tff(c_221651,plain,
    ( ~ r2_hidden(k4_tarski('#skF_4'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')),'#skF_7'),u1_orders_2('#skF_5'))
    | r7_relat_2(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_221387,c_221505])).

tff(c_221652,plain,(
    ~ r2_hidden(k4_tarski('#skF_4'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')),'#skF_7'),u1_orders_2('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_179292,c_221651])).

tff(c_221674,plain,
    ( ~ r1_orders_2('#skF_5','#skF_4'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')),'#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_4'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')),u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_221652])).

tff(c_221692,plain,
    ( ~ r1_orders_2('#skF_5','#skF_4'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')),'#skF_7')
    | ~ m1_subset_1('#skF_4'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')),u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_60,c_221674])).

tff(c_221726,plain,(
    ~ m1_subset_1('#skF_4'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')),u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_221692])).

tff(c_221764,plain,
    ( r7_relat_2(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7'))
    | ~ v1_relat_1(u1_orders_2('#skF_5')) ),
    inference(resolution,[status(thm)],[c_130758,c_221726])).

tff(c_221787,plain,(
    r7_relat_2(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_221387,c_221764])).

tff(c_221789,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_179292,c_221787])).

tff(c_221791,plain,(
    m1_subset_1('#skF_4'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')),u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_221692])).

tff(c_221508,plain,
    ( ~ r2_hidden(k4_tarski('#skF_7','#skF_4'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7'))),u1_orders_2('#skF_5'))
    | r7_relat_2(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7'))
    | ~ v1_relat_1(u1_orders_2('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_221495,c_32])).

tff(c_221654,plain,
    ( ~ r2_hidden(k4_tarski('#skF_7','#skF_4'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7'))),u1_orders_2('#skF_5'))
    | r7_relat_2(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_221387,c_221508])).

tff(c_221655,plain,(
    ~ r2_hidden(k4_tarski('#skF_7','#skF_4'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7'))),u1_orders_2('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_179292,c_221654])).

tff(c_221707,plain,
    ( ~ r1_orders_2('#skF_5','#skF_7','#skF_4'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')))
    | ~ m1_subset_1('#skF_4'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')),u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_221655])).

tff(c_221725,plain,
    ( ~ r1_orders_2('#skF_5','#skF_7','#skF_4'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')))
    | ~ m1_subset_1('#skF_4'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')),u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_60,c_221707])).

tff(c_222659,plain,(
    ~ r1_orders_2('#skF_5','#skF_7','#skF_4'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_221791,c_221725])).

tff(c_233530,plain,(
    ~ r1_orders_2('#skF_5','#skF_7','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_233521,c_222659])).

tff(c_233547,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_209105,c_233530])).

tff(c_233548,plain,(
    '#skF_4'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')) = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_233520])).

tff(c_233683,plain,(
    ~ r1_orders_2('#skF_5','#skF_7','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_233548,c_222659])).

tff(c_233699,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_209101,c_233683])).

tff(c_233700,plain,(
    '#skF_3'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')) = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_221386])).

tff(c_233711,plain,
    ( ~ r2_hidden(k4_tarski('#skF_4'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')),'#skF_6'),u1_orders_2('#skF_5'))
    | r7_relat_2(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7'))
    | ~ v1_relat_1(u1_orders_2('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_233700,c_30])).

tff(c_233857,plain,
    ( ~ r2_hidden(k4_tarski('#skF_4'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')),'#skF_6'),u1_orders_2('#skF_5'))
    | r7_relat_2(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_221387,c_233711])).

tff(c_233858,plain,(
    ~ r2_hidden(k4_tarski('#skF_4'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')),'#skF_6'),u1_orders_2('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_179292,c_233857])).

tff(c_233881,plain,
    ( ~ r1_orders_2('#skF_5','#skF_4'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')),'#skF_6')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_4'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')),u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_233858])).

tff(c_233899,plain,
    ( ~ r1_orders_2('#skF_5','#skF_4'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')),'#skF_6')
    | ~ m1_subset_1('#skF_4'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')),u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_233881])).

tff(c_233933,plain,(
    ~ m1_subset_1('#skF_4'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')),u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_233899])).

tff(c_233971,plain,
    ( r7_relat_2(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7'))
    | ~ v1_relat_1(u1_orders_2('#skF_5')) ),
    inference(resolution,[status(thm)],[c_130758,c_233933])).

tff(c_233994,plain,(
    r7_relat_2(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_221387,c_233971])).

tff(c_233996,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_179292,c_233994])).

tff(c_233998,plain,(
    m1_subset_1('#skF_4'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')),u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_233899])).

tff(c_233714,plain,
    ( ~ r2_hidden(k4_tarski('#skF_6','#skF_4'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7'))),u1_orders_2('#skF_5'))
    | r7_relat_2(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7'))
    | ~ v1_relat_1(u1_orders_2('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_233700,c_32])).

tff(c_233860,plain,
    ( ~ r2_hidden(k4_tarski('#skF_6','#skF_4'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7'))),u1_orders_2('#skF_5'))
    | r7_relat_2(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_221387,c_233714])).

tff(c_233861,plain,(
    ~ r2_hidden(k4_tarski('#skF_6','#skF_4'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7'))),u1_orders_2('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_179292,c_233860])).

tff(c_233914,plain,
    ( ~ r1_orders_2('#skF_5','#skF_6','#skF_4'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')))
    | ~ m1_subset_1('#skF_4'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')),u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_233861])).

tff(c_233932,plain,
    ( ~ r1_orders_2('#skF_5','#skF_6','#skF_4'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')))
    | ~ m1_subset_1('#skF_4'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')),u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_233914])).

tff(c_234866,plain,(
    ~ r1_orders_2('#skF_5','#skF_6','#skF_4'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_233998,c_233932])).

tff(c_241270,plain,(
    ~ r1_orders_2('#skF_5','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_241262,c_234866])).

tff(c_241285,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_209097,c_241270])).

tff(c_241286,plain,(
    '#skF_4'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')) = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_241261])).

tff(c_209752,plain,(
    ! [B_150605] :
      ( r3_orders_2('#skF_5',B_150605,'#skF_7')
      | ~ r1_orders_2('#skF_5',B_150605,'#skF_7')
      | ~ m1_subset_1(B_150605,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_209751])).

tff(c_234162,plain,
    ( r3_orders_2('#skF_5','#skF_4'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')),'#skF_7')
    | ~ r1_orders_2('#skF_5','#skF_4'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')),'#skF_7') ),
    inference(resolution,[status(thm)],[c_233998,c_209752])).

tff(c_236050,plain,(
    ~ r1_orders_2('#skF_5','#skF_4'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_234162])).

tff(c_241302,plain,(
    ~ r1_orders_2('#skF_5','#skF_7','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_241286,c_236050])).

tff(c_241318,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_209101,c_241302])).

tff(c_241320,plain,(
    r1_orders_2('#skF_5','#skF_4'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_234162])).

tff(c_242518,plain,(
    r1_orders_2('#skF_5','#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_242514,c_241320])).

tff(c_242535,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_209793,c_242518])).

tff(c_242536,plain,(
    '#skF_4'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')) = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_242513])).

tff(c_233997,plain,(
    ~ r1_orders_2('#skF_5','#skF_4'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_233899])).

tff(c_242660,plain,(
    ~ r1_orders_2('#skF_5','#skF_7','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_242536,c_233997])).

tff(c_242675,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_209105,c_242660])).

tff(c_242677,plain,(
    v6_orders_2(k2_tarski('#skF_6','#skF_7'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_130709])).

tff(c_130631,plain,(
    ! [B_90175] :
      ( k7_domain_1(u1_struct_0('#skF_5'),B_90175,'#skF_7') = k2_tarski(B_90175,'#skF_7')
      | ~ m1_subset_1(B_90175,u1_struct_0('#skF_5'))
      | v1_xboole_0(u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_60,c_130620])).

tff(c_242703,plain,(
    ! [B_174030] :
      ( k7_domain_1(u1_struct_0('#skF_5'),B_174030,'#skF_7') = k2_tarski(B_174030,'#skF_7')
      | ~ m1_subset_1(B_174030,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_130674,c_130631])).

tff(c_242711,plain,(
    k7_domain_1(u1_struct_0('#skF_5'),'#skF_6','#skF_7') = k2_tarski('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_62,c_242703])).

tff(c_70,plain,
    ( ~ r3_orders_2('#skF_5','#skF_7','#skF_6')
    | ~ m1_subset_1(k7_domain_1(u1_struct_0('#skF_5'),'#skF_6','#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ v6_orders_2(k7_domain_1(u1_struct_0('#skF_5'),'#skF_6','#skF_7'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_130657,plain,
    ( ~ m1_subset_1(k7_domain_1(u1_struct_0('#skF_5'),'#skF_6','#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ v6_orders_2(k7_domain_1(u1_struct_0('#skF_5'),'#skF_6','#skF_7'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_130563,c_70])).

tff(c_130658,plain,(
    ~ v6_orders_2(k7_domain_1(u1_struct_0('#skF_5'),'#skF_6','#skF_7'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_130657])).

tff(c_243402,plain,(
    ~ v6_orders_2(k2_tarski('#skF_6','#skF_7'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_242711,c_130658])).

tff(c_243405,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_242677,c_243402])).

tff(c_243406,plain,(
    ~ m1_subset_1(k7_domain_1(u1_struct_0('#skF_5'),'#skF_6','#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_130657])).

tff(c_243410,plain,
    ( ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_42,c_243406])).

tff(c_243413,plain,(
    v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_243410])).

tff(c_243417,plain,
    ( ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_243413,c_48])).

tff(c_243420,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_243417])).

tff(c_243423,plain,(
    ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_44,c_243420])).

tff(c_243427,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_243423])).

tff(c_243429,plain,(
    ~ r3_orders_2('#skF_5','#skF_7','#skF_6') ),
    inference(splitRight,[status(thm)],[c_130562])).

tff(c_317345,plain,(
    ! [B_232401] :
      ( r3_orders_2('#skF_5',B_232401,'#skF_6')
      | ~ r1_orders_2('#skF_5',B_232401,'#skF_6')
      | ~ m1_subset_1(B_232401,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_62,c_317338])).

tff(c_317352,plain,(
    ! [B_232401] :
      ( r3_orders_2('#skF_5',B_232401,'#skF_6')
      | ~ r1_orders_2('#skF_5',B_232401,'#skF_6')
      | ~ m1_subset_1(B_232401,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_317345])).

tff(c_317366,plain,(
    ! [B_232602] :
      ( r3_orders_2('#skF_5',B_232602,'#skF_6')
      | ~ r1_orders_2('#skF_5',B_232602,'#skF_6')
      | ~ m1_subset_1(B_232602,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_317352])).

tff(c_317369,plain,
    ( r3_orders_2('#skF_5','#skF_7','#skF_6')
    | ~ r1_orders_2('#skF_5','#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_60,c_317366])).

tff(c_317375,plain,(
    ~ r1_orders_2('#skF_5','#skF_7','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_243429,c_317369])).

tff(c_243476,plain,(
    ! [A_175188] :
      ( m1_subset_1(u1_orders_2(A_175188),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_175188),u1_struct_0(A_175188))))
      | ~ l1_orders_2(A_175188) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_243483,plain,(
    ! [A_175188] :
      ( v1_relat_1(u1_orders_2(A_175188))
      | ~ l1_orders_2(A_175188) ) ),
    inference(resolution,[status(thm)],[c_243476,c_2])).

tff(c_243516,plain,(
    ! [A_175204,B_175205,C_175206] :
      ( k7_domain_1(A_175204,B_175205,C_175206) = k2_tarski(B_175205,C_175206)
      | ~ m1_subset_1(C_175206,A_175204)
      | ~ m1_subset_1(B_175205,A_175204)
      | v1_xboole_0(A_175204) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_243530,plain,(
    ! [B_175205] :
      ( k7_domain_1(u1_struct_0('#skF_5'),B_175205,'#skF_7') = k2_tarski(B_175205,'#skF_7')
      | ~ m1_subset_1(B_175205,u1_struct_0('#skF_5'))
      | v1_xboole_0(u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_60,c_243516])).

tff(c_243556,plain,(
    v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_243530])).

tff(c_243559,plain,
    ( ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_243556,c_48])).

tff(c_243562,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_243559])).

tff(c_243565,plain,(
    ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_44,c_243562])).

tff(c_243569,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_243565])).

tff(c_243576,plain,(
    ! [B_175216] :
      ( k7_domain_1(u1_struct_0('#skF_5'),B_175216,'#skF_7') = k2_tarski(B_175216,'#skF_7')
      | ~ m1_subset_1(B_175216,u1_struct_0('#skF_5')) ) ),
    inference(splitRight,[status(thm)],[c_243530])).

tff(c_243584,plain,(
    k7_domain_1(u1_struct_0('#skF_5'),'#skF_6','#skF_7') = k2_tarski('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_62,c_243576])).

tff(c_130541,plain,
    ( r3_orders_2('#skF_5','#skF_7','#skF_6')
    | v6_orders_2(k7_domain_1(u1_struct_0('#skF_5'),'#skF_6','#skF_7'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_243475,plain,(
    v6_orders_2(k7_domain_1(u1_struct_0('#skF_5'),'#skF_6','#skF_7'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_243429,c_130541])).

tff(c_243428,plain,(
    m1_subset_1(k7_domain_1(u1_struct_0('#skF_5'),'#skF_6','#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_130562])).

tff(c_243497,plain,(
    ! [A_175193,B_175194] :
      ( r7_relat_2(u1_orders_2(A_175193),B_175194)
      | ~ v6_orders_2(B_175194,A_175193)
      | ~ m1_subset_1(B_175194,k1_zfmisc_1(u1_struct_0(A_175193)))
      | ~ l1_orders_2(A_175193) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_243500,plain,
    ( r7_relat_2(u1_orders_2('#skF_5'),k7_domain_1(u1_struct_0('#skF_5'),'#skF_6','#skF_7'))
    | ~ v6_orders_2(k7_domain_1(u1_struct_0('#skF_5'),'#skF_6','#skF_7'),'#skF_5')
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_243428,c_243497])).

tff(c_243503,plain,(
    r7_relat_2(u1_orders_2('#skF_5'),k7_domain_1(u1_struct_0('#skF_5'),'#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_243475,c_243500])).

tff(c_243605,plain,(
    r7_relat_2(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_243584,c_243503])).

tff(c_14,plain,(
    ! [D_14,B_10] : r2_hidden(D_14,k2_tarski(D_14,B_10)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_317310,plain,(
    ! [D_232264,C_232265,A_232266,B_232267] :
      ( r2_hidden(k4_tarski(D_232264,C_232265),A_232266)
      | r2_hidden(k4_tarski(C_232265,D_232264),A_232266)
      | ~ r2_hidden(D_232264,B_232267)
      | ~ r2_hidden(C_232265,B_232267)
      | ~ r7_relat_2(A_232266,B_232267)
      | ~ v1_relat_1(A_232266) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_342588,plain,(
    ! [D_253320,C_253321,A_253322,B_253323] :
      ( r2_hidden(k4_tarski(D_253320,C_253321),A_253322)
      | r2_hidden(k4_tarski(C_253321,D_253320),A_253322)
      | ~ r2_hidden(C_253321,k2_tarski(D_253320,B_253323))
      | ~ r7_relat_2(A_253322,k2_tarski(D_253320,B_253323))
      | ~ v1_relat_1(A_253322) ) ),
    inference(resolution,[status(thm)],[c_14,c_317310])).

tff(c_342632,plain,(
    ! [D_253478,A_253479,B_253480] :
      ( r2_hidden(k4_tarski(D_253478,D_253478),A_253479)
      | ~ r7_relat_2(A_253479,k2_tarski(D_253478,B_253480))
      | ~ v1_relat_1(A_253479) ) ),
    inference(resolution,[status(thm)],[c_14,c_342588])).

tff(c_342686,plain,
    ( r2_hidden(k4_tarski('#skF_6','#skF_6'),u1_orders_2('#skF_5'))
    | ~ v1_relat_1(u1_orders_2('#skF_5')) ),
    inference(resolution,[status(thm)],[c_243605,c_342632])).

tff(c_342687,plain,(
    ~ v1_relat_1(u1_orders_2('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_342686])).

tff(c_342692,plain,(
    ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_243483,c_342687])).

tff(c_342696,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_342692])).

tff(c_342698,plain,(
    v1_relat_1(u1_orders_2('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_342686])).

tff(c_12,plain,(
    ! [D_14,A_9] : r2_hidden(D_14,k2_tarski(A_9,D_14)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_343328,plain,(
    ! [A_255188,D_255189,A_255190] :
      ( r2_hidden(k4_tarski(A_255188,D_255189),A_255190)
      | r2_hidden(k4_tarski(D_255189,A_255188),A_255190)
      | ~ r7_relat_2(A_255190,k2_tarski(A_255188,D_255189))
      | ~ v1_relat_1(A_255190) ) ),
    inference(resolution,[status(thm)],[c_12,c_342588])).

tff(c_343383,plain,
    ( r2_hidden(k4_tarski('#skF_6','#skF_7'),u1_orders_2('#skF_5'))
    | r2_hidden(k4_tarski('#skF_7','#skF_6'),u1_orders_2('#skF_5'))
    | ~ v1_relat_1(u1_orders_2('#skF_5')) ),
    inference(resolution,[status(thm)],[c_243605,c_343328])).

tff(c_343404,plain,
    ( r2_hidden(k4_tarski('#skF_6','#skF_7'),u1_orders_2('#skF_5'))
    | r2_hidden(k4_tarski('#skF_7','#skF_6'),u1_orders_2('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_342698,c_343383])).

tff(c_343405,plain,(
    r2_hidden(k4_tarski('#skF_7','#skF_6'),u1_orders_2('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_343404])).

tff(c_38,plain,(
    ! [A_32,B_36,C_38] :
      ( r1_orders_2(A_32,B_36,C_38)
      | ~ r2_hidden(k4_tarski(B_36,C_38),u1_orders_2(A_32))
      | ~ m1_subset_1(C_38,u1_struct_0(A_32))
      | ~ m1_subset_1(B_36,u1_struct_0(A_32))
      | ~ l1_orders_2(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_343420,plain,
    ( r1_orders_2('#skF_5','#skF_7','#skF_6')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_343405,c_38])).

tff(c_343438,plain,(
    r1_orders_2('#skF_5','#skF_7','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_60,c_62,c_343420])).

tff(c_343440,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_317375,c_343438])).

tff(c_343441,plain,(
    r2_hidden(k4_tarski('#skF_6','#skF_7'),u1_orders_2('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_343404])).

tff(c_343457,plain,
    ( r1_orders_2('#skF_5','#skF_6','#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_343441,c_38])).

tff(c_343475,plain,(
    r1_orders_2('#skF_5','#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_343457])).

tff(c_343477,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_317365,c_343475])).

%------------------------------------------------------------------------------
