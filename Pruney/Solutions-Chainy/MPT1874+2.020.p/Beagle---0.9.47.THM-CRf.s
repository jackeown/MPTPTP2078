%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:39 EST 2020

% Result     : Theorem 6.99s
% Output     : CNFRefutation 6.99s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 236 expanded)
%              Number of leaves         :   43 ( 102 expanded)
%              Depth                    :   13
%              Number of atoms          :  167 ( 659 expanded)
%              Number of equality atoms :   30 ( 105 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k9_subset_1 > k1_enumset1 > k6_domain_1 > k3_xboole_0 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_162,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v2_tex_2(B,A)
             => ! [C] :
                  ( m1_subset_1(C,u1_struct_0(A))
                 => ( r2_hidden(C,B)
                   => k9_subset_1(u1_struct_0(A),B,k2_pre_topc(A,k6_domain_1(u1_struct_0(A),C))) = k6_domain_1(u1_struct_0(A),C) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_tex_2)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k9_subset_1(A,C,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_102,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_123,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tex_2(B,A)
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ~ ( r2_hidden(C,B)
                    & ! [D] :
                        ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                       => ~ ( v4_pre_topc(D,A)
                            & k9_subset_1(u1_struct_0(A),B,D) = k1_tarski(C) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_tex_2)).

tff(f_78,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( ! [D] :
                ( m1_subset_1(D,A)
               => ( r2_hidden(D,B)
                 => r2_hidden(D,C) ) )
           => r1_tarski(B,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_subset_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => m1_subset_1(k9_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).

tff(f_142,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tex_2(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( r1_tarski(C,B)
                 => k9_subset_1(u1_struct_0(A),B,k2_pre_topc(A,C)) = C ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_tex_2)).

tff(f_95,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(c_68,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_1859,plain,(
    ! [A_294,B_295,C_296] :
      ( k9_subset_1(A_294,B_295,C_296) = k3_xboole_0(B_295,C_296)
      | ~ m1_subset_1(C_296,k1_zfmisc_1(A_294)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1869,plain,(
    ! [B_295] : k9_subset_1(u1_struct_0('#skF_4'),B_295,'#skF_5') = k3_xboole_0(B_295,'#skF_5') ),
    inference(resolution,[status(thm)],[c_68,c_1859])).

tff(c_2065,plain,(
    ! [A_329,C_330,B_331] :
      ( k9_subset_1(A_329,C_330,B_331) = k9_subset_1(A_329,B_331,C_330)
      | ~ m1_subset_1(C_330,k1_zfmisc_1(A_329)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2076,plain,(
    ! [B_331] : k9_subset_1(u1_struct_0('#skF_4'),B_331,'#skF_5') = k9_subset_1(u1_struct_0('#skF_4'),'#skF_5',B_331) ),
    inference(resolution,[status(thm)],[c_68,c_2065])).

tff(c_2082,plain,(
    ! [B_331] : k9_subset_1(u1_struct_0('#skF_4'),'#skF_5',B_331) = k3_xboole_0(B_331,'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1869,c_2076])).

tff(c_64,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_98,plain,(
    ! [B_90,A_91] :
      ( v1_xboole_0(B_90)
      | ~ m1_subset_1(B_90,A_91)
      | ~ v1_xboole_0(A_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_106,plain,
    ( v1_xboole_0('#skF_6')
    | ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_64,c_98])).

tff(c_107,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_106])).

tff(c_1779,plain,(
    ! [A_283,B_284] :
      ( k6_domain_1(A_283,B_284) = k1_tarski(B_284)
      | ~ m1_subset_1(B_284,A_283)
      | v1_xboole_0(A_283) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_1794,plain,
    ( k6_domain_1(u1_struct_0('#skF_4'),'#skF_6') = k1_tarski('#skF_6')
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_64,c_1779])).

tff(c_1805,plain,(
    k6_domain_1(u1_struct_0('#skF_4'),'#skF_6') = k1_tarski('#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_107,c_1794])).

tff(c_60,plain,(
    k9_subset_1(u1_struct_0('#skF_4'),'#skF_5',k2_pre_topc('#skF_4',k6_domain_1(u1_struct_0('#skF_4'),'#skF_6'))) != k6_domain_1(u1_struct_0('#skF_4'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_1815,plain,(
    k9_subset_1(u1_struct_0('#skF_4'),'#skF_5',k2_pre_topc('#skF_4',k1_tarski('#skF_6'))) != k1_tarski('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1805,c_1805,c_60])).

tff(c_2083,plain,(
    k3_xboole_0(k2_pre_topc('#skF_4',k1_tarski('#skF_6')),'#skF_5') != k1_tarski('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2082,c_1815])).

tff(c_66,plain,(
    v2_tex_2('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_62,plain,(
    r2_hidden('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_70,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_4178,plain,(
    ! [A_498,B_499,C_500] :
      ( k9_subset_1(u1_struct_0(A_498),B_499,'#skF_2'(A_498,B_499,C_500)) = k1_tarski(C_500)
      | ~ r2_hidden(C_500,B_499)
      | ~ m1_subset_1(C_500,u1_struct_0(A_498))
      | ~ v2_tex_2(B_499,A_498)
      | ~ m1_subset_1(B_499,k1_zfmisc_1(u1_struct_0(A_498)))
      | ~ l1_pre_topc(A_498) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_4204,plain,(
    ! [C_500] :
      ( k9_subset_1(u1_struct_0('#skF_4'),'#skF_5','#skF_2'('#skF_4','#skF_5',C_500)) = k1_tarski(C_500)
      | ~ r2_hidden(C_500,'#skF_5')
      | ~ m1_subset_1(C_500,u1_struct_0('#skF_4'))
      | ~ v2_tex_2('#skF_5','#skF_4')
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_68,c_4178])).

tff(c_5046,plain,(
    ! [C_519] :
      ( k3_xboole_0('#skF_2'('#skF_4','#skF_5',C_519),'#skF_5') = k1_tarski(C_519)
      | ~ r2_hidden(C_519,'#skF_5')
      | ~ m1_subset_1(C_519,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_2082,c_4204])).

tff(c_5063,plain,
    ( k3_xboole_0('#skF_2'('#skF_4','#skF_5','#skF_6'),'#skF_5') = k1_tarski('#skF_6')
    | ~ r2_hidden('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_64,c_5046])).

tff(c_5070,plain,(
    k3_xboole_0('#skF_2'('#skF_4','#skF_5','#skF_6'),'#skF_5') = k1_tarski('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_5063])).

tff(c_32,plain,(
    ! [A_40,B_41,C_45] :
      ( r2_hidden('#skF_1'(A_40,B_41,C_45),B_41)
      | r1_tarski(B_41,C_45)
      | ~ m1_subset_1(C_45,k1_zfmisc_1(A_40))
      | ~ m1_subset_1(B_41,k1_zfmisc_1(A_40)) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_2957,plain,(
    ! [A_418,B_419,C_420] :
      ( ~ r2_hidden('#skF_1'(A_418,B_419,C_420),C_420)
      | r1_tarski(B_419,C_420)
      | ~ m1_subset_1(C_420,k1_zfmisc_1(A_418))
      | ~ m1_subset_1(B_419,k1_zfmisc_1(A_418)) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_2968,plain,(
    ! [B_421,A_422] :
      ( r1_tarski(B_421,B_421)
      | ~ m1_subset_1(B_421,k1_zfmisc_1(A_422)) ) ),
    inference(resolution,[status(thm)],[c_32,c_2957])).

tff(c_2997,plain,(
    r1_tarski('#skF_5','#skF_5') ),
    inference(resolution,[status(thm)],[c_68,c_2968])).

tff(c_38,plain,(
    ! [A_47,B_48] :
      ( m1_subset_1(A_47,k1_zfmisc_1(B_48))
      | ~ r1_tarski(A_47,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1868,plain,(
    ! [B_48,B_295,A_47] :
      ( k9_subset_1(B_48,B_295,A_47) = k3_xboole_0(B_295,A_47)
      | ~ r1_tarski(A_47,B_48) ) ),
    inference(resolution,[status(thm)],[c_38,c_1859])).

tff(c_3054,plain,(
    ! [B_425] : k9_subset_1('#skF_5',B_425,'#skF_5') = k3_xboole_0(B_425,'#skF_5') ),
    inference(resolution,[status(thm)],[c_2997,c_1868])).

tff(c_1901,plain,(
    ! [A_299,B_300,C_301] :
      ( m1_subset_1(k9_subset_1(A_299,B_300,C_301),k1_zfmisc_1(A_299))
      | ~ m1_subset_1(C_301,k1_zfmisc_1(A_299)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_36,plain,(
    ! [A_47,B_48] :
      ( r1_tarski(A_47,B_48)
      | ~ m1_subset_1(A_47,k1_zfmisc_1(B_48)) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1925,plain,(
    ! [A_299,B_300,C_301] :
      ( r1_tarski(k9_subset_1(A_299,B_300,C_301),A_299)
      | ~ m1_subset_1(C_301,k1_zfmisc_1(A_299)) ) ),
    inference(resolution,[status(thm)],[c_1901,c_36])).

tff(c_3072,plain,(
    ! [B_425] :
      ( r1_tarski(k3_xboole_0(B_425,'#skF_5'),'#skF_5')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3054,c_1925])).

tff(c_3238,plain,(
    ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_3072])).

tff(c_3244,plain,(
    ~ r1_tarski('#skF_5','#skF_5') ),
    inference(resolution,[status(thm)],[c_38,c_3238])).

tff(c_3249,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2997,c_3244])).

tff(c_3250,plain,(
    ! [B_425] : r1_tarski(k3_xboole_0(B_425,'#skF_5'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_3072])).

tff(c_5164,plain,(
    r1_tarski(k1_tarski('#skF_6'),'#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_5070,c_3250])).

tff(c_74,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_72,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_1919,plain,(
    ! [B_295] :
      ( m1_subset_1(k3_xboole_0(B_295,'#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1869,c_1901])).

tff(c_1927,plain,(
    ! [B_295] : m1_subset_1(k3_xboole_0(B_295,'#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_1919])).

tff(c_5213,plain,(
    m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_5070,c_1927])).

tff(c_52,plain,(
    ! [A_71,B_77,C_80] :
      ( k9_subset_1(u1_struct_0(A_71),B_77,k2_pre_topc(A_71,C_80)) = C_80
      | ~ r1_tarski(C_80,B_77)
      | ~ m1_subset_1(C_80,k1_zfmisc_1(u1_struct_0(A_71)))
      | ~ v2_tex_2(B_77,A_71)
      | ~ m1_subset_1(B_77,k1_zfmisc_1(u1_struct_0(A_71)))
      | ~ l1_pre_topc(A_71)
      | ~ v2_pre_topc(A_71)
      | v2_struct_0(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_5402,plain,(
    ! [B_77] :
      ( k9_subset_1(u1_struct_0('#skF_4'),B_77,k2_pre_topc('#skF_4',k1_tarski('#skF_6'))) = k1_tarski('#skF_6')
      | ~ r1_tarski(k1_tarski('#skF_6'),B_77)
      | ~ v2_tex_2(B_77,'#skF_4')
      | ~ m1_subset_1(B_77,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_5213,c_52])).

tff(c_5431,plain,(
    ! [B_77] :
      ( k9_subset_1(u1_struct_0('#skF_4'),B_77,k2_pre_topc('#skF_4',k1_tarski('#skF_6'))) = k1_tarski('#skF_6')
      | ~ r1_tarski(k1_tarski('#skF_6'),B_77)
      | ~ v2_tex_2(B_77,'#skF_4')
      | ~ m1_subset_1(B_77,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_5402])).

tff(c_6044,plain,(
    ! [B_542] :
      ( k9_subset_1(u1_struct_0('#skF_4'),B_542,k2_pre_topc('#skF_4',k1_tarski('#skF_6'))) = k1_tarski('#skF_6')
      | ~ r1_tarski(k1_tarski('#skF_6'),B_542)
      | ~ v2_tex_2(B_542,'#skF_4')
      | ~ m1_subset_1(B_542,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_5431])).

tff(c_6067,plain,
    ( k3_xboole_0(k2_pre_topc('#skF_4',k1_tarski('#skF_6')),'#skF_5') = k1_tarski('#skF_6')
    | ~ r1_tarski(k1_tarski('#skF_6'),'#skF_5')
    | ~ v2_tex_2('#skF_5','#skF_4')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_6044,c_2082])).

tff(c_6089,plain,(
    k3_xboole_0(k2_pre_topc('#skF_4',k1_tarski('#skF_6')),'#skF_5') = k1_tarski('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_5164,c_6067])).

tff(c_6091,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2083,c_6089])).

tff(c_6093,plain,(
    v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_106])).

tff(c_6127,plain,(
    ! [C_555,B_556,A_557] :
      ( ~ v1_xboole_0(C_555)
      | ~ m1_subset_1(B_556,k1_zfmisc_1(C_555))
      | ~ r2_hidden(A_557,B_556) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_6134,plain,(
    ! [A_557] :
      ( ~ v1_xboole_0(u1_struct_0('#skF_4'))
      | ~ r2_hidden(A_557,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_68,c_6127])).

tff(c_6139,plain,(
    ! [A_557] : ~ r2_hidden(A_557,'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6093,c_6134])).

tff(c_6141,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6139,c_62])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 13:50:57 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.99/2.48  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.99/2.49  
% 6.99/2.49  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.99/2.49  %$ v4_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k9_subset_1 > k1_enumset1 > k6_domain_1 > k3_xboole_0 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4
% 6.99/2.49  
% 6.99/2.49  %Foreground sorts:
% 6.99/2.49  
% 6.99/2.49  
% 6.99/2.49  %Background operators:
% 6.99/2.49  
% 6.99/2.49  
% 6.99/2.49  %Foreground operators:
% 6.99/2.49  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 6.99/2.49  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 6.99/2.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.99/2.49  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.99/2.49  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.99/2.49  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 6.99/2.49  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 6.99/2.49  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 6.99/2.49  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 6.99/2.49  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.99/2.49  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.99/2.49  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.99/2.49  tff('#skF_5', type, '#skF_5': $i).
% 6.99/2.49  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 6.99/2.49  tff('#skF_6', type, '#skF_6': $i).
% 6.99/2.49  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.99/2.49  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 6.99/2.49  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.99/2.49  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.99/2.49  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 6.99/2.49  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 6.99/2.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.99/2.49  tff('#skF_4', type, '#skF_4': $i).
% 6.99/2.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.99/2.49  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 6.99/2.49  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.99/2.49  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 6.99/2.49  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 6.99/2.49  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.99/2.49  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 6.99/2.49  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 6.99/2.49  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.99/2.49  
% 6.99/2.51  tff(f_162, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(C, B) => (k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, k6_domain_1(u1_struct_0(A), C))) = k6_domain_1(u1_struct_0(A), C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_tex_2)).
% 6.99/2.51  tff(f_64, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 6.99/2.51  tff(f_43, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k9_subset_1(A, C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k9_subset_1)).
% 6.99/2.51  tff(f_56, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 6.99/2.51  tff(f_102, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 6.99/2.51  tff(f_123, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ~(r2_hidden(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v4_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = k1_tarski(C))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_tex_2)).
% 6.99/2.51  tff(f_78, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((![D]: (m1_subset_1(D, A) => (r2_hidden(D, B) => r2_hidden(D, C)))) => r1_tarski(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_subset_1)).
% 6.99/2.51  tff(f_82, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 6.99/2.51  tff(f_60, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => m1_subset_1(k9_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 6.99/2.51  tff(f_142, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(C, B) => (k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, C)) = C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_tex_2)).
% 6.99/2.51  tff(f_95, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 6.99/2.51  tff(c_68, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_162])).
% 6.99/2.51  tff(c_1859, plain, (![A_294, B_295, C_296]: (k9_subset_1(A_294, B_295, C_296)=k3_xboole_0(B_295, C_296) | ~m1_subset_1(C_296, k1_zfmisc_1(A_294)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 6.99/2.51  tff(c_1869, plain, (![B_295]: (k9_subset_1(u1_struct_0('#skF_4'), B_295, '#skF_5')=k3_xboole_0(B_295, '#skF_5'))), inference(resolution, [status(thm)], [c_68, c_1859])).
% 6.99/2.51  tff(c_2065, plain, (![A_329, C_330, B_331]: (k9_subset_1(A_329, C_330, B_331)=k9_subset_1(A_329, B_331, C_330) | ~m1_subset_1(C_330, k1_zfmisc_1(A_329)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.99/2.51  tff(c_2076, plain, (![B_331]: (k9_subset_1(u1_struct_0('#skF_4'), B_331, '#skF_5')=k9_subset_1(u1_struct_0('#skF_4'), '#skF_5', B_331))), inference(resolution, [status(thm)], [c_68, c_2065])).
% 6.99/2.51  tff(c_2082, plain, (![B_331]: (k9_subset_1(u1_struct_0('#skF_4'), '#skF_5', B_331)=k3_xboole_0(B_331, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_1869, c_2076])).
% 6.99/2.51  tff(c_64, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_162])).
% 6.99/2.51  tff(c_98, plain, (![B_90, A_91]: (v1_xboole_0(B_90) | ~m1_subset_1(B_90, A_91) | ~v1_xboole_0(A_91))), inference(cnfTransformation, [status(thm)], [f_56])).
% 6.99/2.51  tff(c_106, plain, (v1_xboole_0('#skF_6') | ~v1_xboole_0(u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_64, c_98])).
% 6.99/2.51  tff(c_107, plain, (~v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_106])).
% 6.99/2.51  tff(c_1779, plain, (![A_283, B_284]: (k6_domain_1(A_283, B_284)=k1_tarski(B_284) | ~m1_subset_1(B_284, A_283) | v1_xboole_0(A_283))), inference(cnfTransformation, [status(thm)], [f_102])).
% 6.99/2.51  tff(c_1794, plain, (k6_domain_1(u1_struct_0('#skF_4'), '#skF_6')=k1_tarski('#skF_6') | v1_xboole_0(u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_64, c_1779])).
% 6.99/2.51  tff(c_1805, plain, (k6_domain_1(u1_struct_0('#skF_4'), '#skF_6')=k1_tarski('#skF_6')), inference(negUnitSimplification, [status(thm)], [c_107, c_1794])).
% 6.99/2.51  tff(c_60, plain, (k9_subset_1(u1_struct_0('#skF_4'), '#skF_5', k2_pre_topc('#skF_4', k6_domain_1(u1_struct_0('#skF_4'), '#skF_6')))!=k6_domain_1(u1_struct_0('#skF_4'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_162])).
% 6.99/2.51  tff(c_1815, plain, (k9_subset_1(u1_struct_0('#skF_4'), '#skF_5', k2_pre_topc('#skF_4', k1_tarski('#skF_6')))!=k1_tarski('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1805, c_1805, c_60])).
% 6.99/2.51  tff(c_2083, plain, (k3_xboole_0(k2_pre_topc('#skF_4', k1_tarski('#skF_6')), '#skF_5')!=k1_tarski('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2082, c_1815])).
% 6.99/2.51  tff(c_66, plain, (v2_tex_2('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_162])).
% 6.99/2.51  tff(c_62, plain, (r2_hidden('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_162])).
% 6.99/2.51  tff(c_70, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_162])).
% 6.99/2.51  tff(c_4178, plain, (![A_498, B_499, C_500]: (k9_subset_1(u1_struct_0(A_498), B_499, '#skF_2'(A_498, B_499, C_500))=k1_tarski(C_500) | ~r2_hidden(C_500, B_499) | ~m1_subset_1(C_500, u1_struct_0(A_498)) | ~v2_tex_2(B_499, A_498) | ~m1_subset_1(B_499, k1_zfmisc_1(u1_struct_0(A_498))) | ~l1_pre_topc(A_498))), inference(cnfTransformation, [status(thm)], [f_123])).
% 6.99/2.51  tff(c_4204, plain, (![C_500]: (k9_subset_1(u1_struct_0('#skF_4'), '#skF_5', '#skF_2'('#skF_4', '#skF_5', C_500))=k1_tarski(C_500) | ~r2_hidden(C_500, '#skF_5') | ~m1_subset_1(C_500, u1_struct_0('#skF_4')) | ~v2_tex_2('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_68, c_4178])).
% 6.99/2.51  tff(c_5046, plain, (![C_519]: (k3_xboole_0('#skF_2'('#skF_4', '#skF_5', C_519), '#skF_5')=k1_tarski(C_519) | ~r2_hidden(C_519, '#skF_5') | ~m1_subset_1(C_519, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_66, c_2082, c_4204])).
% 6.99/2.51  tff(c_5063, plain, (k3_xboole_0('#skF_2'('#skF_4', '#skF_5', '#skF_6'), '#skF_5')=k1_tarski('#skF_6') | ~r2_hidden('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_64, c_5046])).
% 6.99/2.51  tff(c_5070, plain, (k3_xboole_0('#skF_2'('#skF_4', '#skF_5', '#skF_6'), '#skF_5')=k1_tarski('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_5063])).
% 6.99/2.51  tff(c_32, plain, (![A_40, B_41, C_45]: (r2_hidden('#skF_1'(A_40, B_41, C_45), B_41) | r1_tarski(B_41, C_45) | ~m1_subset_1(C_45, k1_zfmisc_1(A_40)) | ~m1_subset_1(B_41, k1_zfmisc_1(A_40)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 6.99/2.51  tff(c_2957, plain, (![A_418, B_419, C_420]: (~r2_hidden('#skF_1'(A_418, B_419, C_420), C_420) | r1_tarski(B_419, C_420) | ~m1_subset_1(C_420, k1_zfmisc_1(A_418)) | ~m1_subset_1(B_419, k1_zfmisc_1(A_418)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 6.99/2.51  tff(c_2968, plain, (![B_421, A_422]: (r1_tarski(B_421, B_421) | ~m1_subset_1(B_421, k1_zfmisc_1(A_422)))), inference(resolution, [status(thm)], [c_32, c_2957])).
% 6.99/2.51  tff(c_2997, plain, (r1_tarski('#skF_5', '#skF_5')), inference(resolution, [status(thm)], [c_68, c_2968])).
% 6.99/2.51  tff(c_38, plain, (![A_47, B_48]: (m1_subset_1(A_47, k1_zfmisc_1(B_48)) | ~r1_tarski(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_82])).
% 6.99/2.51  tff(c_1868, plain, (![B_48, B_295, A_47]: (k9_subset_1(B_48, B_295, A_47)=k3_xboole_0(B_295, A_47) | ~r1_tarski(A_47, B_48))), inference(resolution, [status(thm)], [c_38, c_1859])).
% 6.99/2.51  tff(c_3054, plain, (![B_425]: (k9_subset_1('#skF_5', B_425, '#skF_5')=k3_xboole_0(B_425, '#skF_5'))), inference(resolution, [status(thm)], [c_2997, c_1868])).
% 6.99/2.51  tff(c_1901, plain, (![A_299, B_300, C_301]: (m1_subset_1(k9_subset_1(A_299, B_300, C_301), k1_zfmisc_1(A_299)) | ~m1_subset_1(C_301, k1_zfmisc_1(A_299)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 6.99/2.51  tff(c_36, plain, (![A_47, B_48]: (r1_tarski(A_47, B_48) | ~m1_subset_1(A_47, k1_zfmisc_1(B_48)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 6.99/2.51  tff(c_1925, plain, (![A_299, B_300, C_301]: (r1_tarski(k9_subset_1(A_299, B_300, C_301), A_299) | ~m1_subset_1(C_301, k1_zfmisc_1(A_299)))), inference(resolution, [status(thm)], [c_1901, c_36])).
% 6.99/2.51  tff(c_3072, plain, (![B_425]: (r1_tarski(k3_xboole_0(B_425, '#skF_5'), '#skF_5') | ~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_3054, c_1925])).
% 6.99/2.51  tff(c_3238, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_3072])).
% 6.99/2.51  tff(c_3244, plain, (~r1_tarski('#skF_5', '#skF_5')), inference(resolution, [status(thm)], [c_38, c_3238])).
% 6.99/2.51  tff(c_3249, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2997, c_3244])).
% 6.99/2.51  tff(c_3250, plain, (![B_425]: (r1_tarski(k3_xboole_0(B_425, '#skF_5'), '#skF_5'))), inference(splitRight, [status(thm)], [c_3072])).
% 6.99/2.51  tff(c_5164, plain, (r1_tarski(k1_tarski('#skF_6'), '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_5070, c_3250])).
% 6.99/2.51  tff(c_74, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_162])).
% 6.99/2.51  tff(c_72, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_162])).
% 6.99/2.51  tff(c_1919, plain, (![B_295]: (m1_subset_1(k3_xboole_0(B_295, '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(superposition, [status(thm), theory('equality')], [c_1869, c_1901])).
% 6.99/2.51  tff(c_1927, plain, (![B_295]: (m1_subset_1(k3_xboole_0(B_295, '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_1919])).
% 6.99/2.51  tff(c_5213, plain, (m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_5070, c_1927])).
% 6.99/2.51  tff(c_52, plain, (![A_71, B_77, C_80]: (k9_subset_1(u1_struct_0(A_71), B_77, k2_pre_topc(A_71, C_80))=C_80 | ~r1_tarski(C_80, B_77) | ~m1_subset_1(C_80, k1_zfmisc_1(u1_struct_0(A_71))) | ~v2_tex_2(B_77, A_71) | ~m1_subset_1(B_77, k1_zfmisc_1(u1_struct_0(A_71))) | ~l1_pre_topc(A_71) | ~v2_pre_topc(A_71) | v2_struct_0(A_71))), inference(cnfTransformation, [status(thm)], [f_142])).
% 6.99/2.51  tff(c_5402, plain, (![B_77]: (k9_subset_1(u1_struct_0('#skF_4'), B_77, k2_pre_topc('#skF_4', k1_tarski('#skF_6')))=k1_tarski('#skF_6') | ~r1_tarski(k1_tarski('#skF_6'), B_77) | ~v2_tex_2(B_77, '#skF_4') | ~m1_subset_1(B_77, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_5213, c_52])).
% 6.99/2.51  tff(c_5431, plain, (![B_77]: (k9_subset_1(u1_struct_0('#skF_4'), B_77, k2_pre_topc('#skF_4', k1_tarski('#skF_6')))=k1_tarski('#skF_6') | ~r1_tarski(k1_tarski('#skF_6'), B_77) | ~v2_tex_2(B_77, '#skF_4') | ~m1_subset_1(B_77, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_5402])).
% 6.99/2.51  tff(c_6044, plain, (![B_542]: (k9_subset_1(u1_struct_0('#skF_4'), B_542, k2_pre_topc('#skF_4', k1_tarski('#skF_6')))=k1_tarski('#skF_6') | ~r1_tarski(k1_tarski('#skF_6'), B_542) | ~v2_tex_2(B_542, '#skF_4') | ~m1_subset_1(B_542, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_74, c_5431])).
% 6.99/2.51  tff(c_6067, plain, (k3_xboole_0(k2_pre_topc('#skF_4', k1_tarski('#skF_6')), '#skF_5')=k1_tarski('#skF_6') | ~r1_tarski(k1_tarski('#skF_6'), '#skF_5') | ~v2_tex_2('#skF_5', '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_6044, c_2082])).
% 6.99/2.51  tff(c_6089, plain, (k3_xboole_0(k2_pre_topc('#skF_4', k1_tarski('#skF_6')), '#skF_5')=k1_tarski('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_5164, c_6067])).
% 6.99/2.51  tff(c_6091, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2083, c_6089])).
% 6.99/2.51  tff(c_6093, plain, (v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_106])).
% 6.99/2.51  tff(c_6127, plain, (![C_555, B_556, A_557]: (~v1_xboole_0(C_555) | ~m1_subset_1(B_556, k1_zfmisc_1(C_555)) | ~r2_hidden(A_557, B_556))), inference(cnfTransformation, [status(thm)], [f_95])).
% 6.99/2.51  tff(c_6134, plain, (![A_557]: (~v1_xboole_0(u1_struct_0('#skF_4')) | ~r2_hidden(A_557, '#skF_5'))), inference(resolution, [status(thm)], [c_68, c_6127])).
% 6.99/2.51  tff(c_6139, plain, (![A_557]: (~r2_hidden(A_557, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_6093, c_6134])).
% 6.99/2.51  tff(c_6141, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6139, c_62])).
% 6.99/2.51  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.99/2.51  
% 6.99/2.51  Inference rules
% 6.99/2.51  ----------------------
% 6.99/2.51  #Ref     : 0
% 6.99/2.51  #Sup     : 1524
% 6.99/2.51  #Fact    : 0
% 6.99/2.51  #Define  : 0
% 6.99/2.51  #Split   : 11
% 6.99/2.51  #Chain   : 0
% 6.99/2.51  #Close   : 0
% 6.99/2.51  
% 6.99/2.51  Ordering : KBO
% 6.99/2.51  
% 6.99/2.51  Simplification rules
% 6.99/2.51  ----------------------
% 6.99/2.51  #Subsume      : 245
% 6.99/2.51  #Demod        : 756
% 6.99/2.51  #Tautology    : 494
% 6.99/2.51  #SimpNegUnit  : 78
% 6.99/2.51  #BackRed      : 6
% 6.99/2.51  
% 6.99/2.51  #Partial instantiations: 0
% 6.99/2.51  #Strategies tried      : 1
% 6.99/2.51  
% 6.99/2.51  Timing (in seconds)
% 6.99/2.51  ----------------------
% 6.99/2.51  Preprocessing        : 0.42
% 6.99/2.51  Parsing              : 0.22
% 6.99/2.51  CNF conversion       : 0.03
% 6.99/2.51  Main loop            : 1.30
% 6.99/2.51  Inferencing          : 0.41
% 6.99/2.51  Reduction            : 0.50
% 6.99/2.51  Demodulation         : 0.36
% 6.99/2.51  BG Simplification    : 0.06
% 6.99/2.51  Subsumption          : 0.23
% 6.99/2.51  Abstraction          : 0.09
% 6.99/2.51  MUC search           : 0.00
% 6.99/2.51  Cooper               : 0.00
% 6.99/2.51  Total                : 1.77
% 6.99/2.51  Index Insertion      : 0.00
% 6.99/2.51  Index Deletion       : 0.00
% 6.99/2.51  Index Matching       : 0.00
% 6.99/2.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
