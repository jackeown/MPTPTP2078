%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:09 EST 2020

% Result     : Theorem 9.48s
% Output     : CNFRefutation 9.72s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 494 expanded)
%              Number of leaves         :   30 ( 185 expanded)
%              Depth                    :   22
%              Number of atoms          :  316 (2267 expanded)
%              Number of equality atoms :    7 (  17 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(m1_connsp_2,type,(
    m1_connsp_2: ( $i * $i * $i ) > $o )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

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

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_173,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ~ ( m1_connsp_2(C,A,B)
                    & ! [D] :
                        ( ( ~ v1_xboole_0(D)
                          & m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A))) )
                       => ~ ( m1_connsp_2(D,A,B)
                            & v3_pre_topc(D,A)
                            & r1_tarski(D,C) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_connsp_2)).

tff(f_126,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_connsp_2)).

tff(f_62,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k1_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tops_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

tff(f_109,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( l1_pre_topc(B)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ! [D] :
                  ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(B)))
                 => ( ( v3_pre_topc(D,B)
                     => k1_tops_1(B,D) = D )
                    & ( k1_tops_1(A,C) = C
                     => v3_pre_topc(C,A) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_tops_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_143,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( m1_connsp_2(B,A,C)
               => r2_hidden(C,B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_connsp_2)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(c_48,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_44,plain,(
    m1_connsp_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_54,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_52,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_50,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_46,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_1782,plain,(
    ! [B_307,A_308,C_309] :
      ( r2_hidden(B_307,k1_tops_1(A_308,C_309))
      | ~ m1_connsp_2(C_309,A_308,B_307)
      | ~ m1_subset_1(C_309,k1_zfmisc_1(u1_struct_0(A_308)))
      | ~ m1_subset_1(B_307,u1_struct_0(A_308))
      | ~ l1_pre_topc(A_308)
      | ~ v2_pre_topc(A_308)
      | v2_struct_0(A_308) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_1797,plain,(
    ! [B_307] :
      ( r2_hidden(B_307,k1_tops_1('#skF_3','#skF_5'))
      | ~ m1_connsp_2('#skF_5','#skF_3',B_307)
      | ~ m1_subset_1(B_307,u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_46,c_1782])).

tff(c_1805,plain,(
    ! [B_307] :
      ( r2_hidden(B_307,k1_tops_1('#skF_3','#skF_5'))
      | ~ m1_connsp_2('#skF_5','#skF_3',B_307)
      | ~ m1_subset_1(B_307,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_1797])).

tff(c_1806,plain,(
    ! [B_307] :
      ( r2_hidden(B_307,k1_tops_1('#skF_3','#skF_5'))
      | ~ m1_connsp_2('#skF_5','#skF_3',B_307)
      | ~ m1_subset_1(B_307,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_1805])).

tff(c_18,plain,(
    ! [A_18,B_19] :
      ( m1_subset_1(k1_tops_1(A_18,B_19),k1_zfmisc_1(u1_struct_0(A_18)))
      | ~ m1_subset_1(B_19,k1_zfmisc_1(u1_struct_0(A_18)))
      | ~ l1_pre_topc(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_279,plain,(
    ! [A_133,B_134] :
      ( v3_pre_topc(k1_tops_1(A_133,B_134),A_133)
      | ~ m1_subset_1(B_134,k1_zfmisc_1(u1_struct_0(A_133)))
      | ~ l1_pre_topc(A_133)
      | ~ v2_pre_topc(A_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_289,plain,
    ( v3_pre_topc(k1_tops_1('#skF_3','#skF_5'),'#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_279])).

tff(c_295,plain,(
    v3_pre_topc(k1_tops_1('#skF_3','#skF_5'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_289])).

tff(c_34,plain,(
    ! [B_42,D_48,C_46,A_34] :
      ( k1_tops_1(B_42,D_48) = D_48
      | ~ v3_pre_topc(D_48,B_42)
      | ~ m1_subset_1(D_48,k1_zfmisc_1(u1_struct_0(B_42)))
      | ~ m1_subset_1(C_46,k1_zfmisc_1(u1_struct_0(A_34)))
      | ~ l1_pre_topc(B_42)
      | ~ l1_pre_topc(A_34)
      | ~ v2_pre_topc(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_1114,plain,(
    ! [C_250,A_251] :
      ( ~ m1_subset_1(C_250,k1_zfmisc_1(u1_struct_0(A_251)))
      | ~ l1_pre_topc(A_251)
      | ~ v2_pre_topc(A_251) ) ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_1132,plain,
    ( ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_1114])).

tff(c_1140,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_1132])).

tff(c_1226,plain,(
    ! [B_257,D_258] :
      ( k1_tops_1(B_257,D_258) = D_258
      | ~ v3_pre_topc(D_258,B_257)
      | ~ m1_subset_1(D_258,k1_zfmisc_1(u1_struct_0(B_257)))
      | ~ l1_pre_topc(B_257) ) ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_2387,plain,(
    ! [A_374,B_375] :
      ( k1_tops_1(A_374,k1_tops_1(A_374,B_375)) = k1_tops_1(A_374,B_375)
      | ~ v3_pre_topc(k1_tops_1(A_374,B_375),A_374)
      | ~ m1_subset_1(B_375,k1_zfmisc_1(u1_struct_0(A_374)))
      | ~ l1_pre_topc(A_374) ) ),
    inference(resolution,[status(thm)],[c_18,c_1226])).

tff(c_2396,plain,
    ( k1_tops_1('#skF_3',k1_tops_1('#skF_3','#skF_5')) = k1_tops_1('#skF_3','#skF_5')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_295,c_2387])).

tff(c_2404,plain,(
    k1_tops_1('#skF_3',k1_tops_1('#skF_3','#skF_5')) = k1_tops_1('#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_2396])).

tff(c_36,plain,(
    ! [C_55,A_49,B_53] :
      ( m1_connsp_2(C_55,A_49,B_53)
      | ~ r2_hidden(B_53,k1_tops_1(A_49,C_55))
      | ~ m1_subset_1(C_55,k1_zfmisc_1(u1_struct_0(A_49)))
      | ~ m1_subset_1(B_53,u1_struct_0(A_49))
      | ~ l1_pre_topc(A_49)
      | ~ v2_pre_topc(A_49)
      | v2_struct_0(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_2419,plain,(
    ! [B_53] :
      ( m1_connsp_2(k1_tops_1('#skF_3','#skF_5'),'#skF_3',B_53)
      | ~ r2_hidden(B_53,k1_tops_1('#skF_3','#skF_5'))
      | ~ m1_subset_1(k1_tops_1('#skF_3','#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(B_53,u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2404,c_36])).

tff(c_2446,plain,(
    ! [B_53] :
      ( m1_connsp_2(k1_tops_1('#skF_3','#skF_5'),'#skF_3',B_53)
      | ~ r2_hidden(B_53,k1_tops_1('#skF_3','#skF_5'))
      | ~ m1_subset_1(k1_tops_1('#skF_3','#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(B_53,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_2419])).

tff(c_2447,plain,(
    ! [B_53] :
      ( m1_connsp_2(k1_tops_1('#skF_3','#skF_5'),'#skF_3',B_53)
      | ~ r2_hidden(B_53,k1_tops_1('#skF_3','#skF_5'))
      | ~ m1_subset_1(k1_tops_1('#skF_3','#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(B_53,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_2446])).

tff(c_2464,plain,(
    ~ m1_subset_1(k1_tops_1('#skF_3','#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_2447])).

tff(c_2467,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_2464])).

tff(c_2474,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_2467])).

tff(c_2700,plain,(
    ! [B_390] :
      ( m1_connsp_2(k1_tops_1('#skF_3','#skF_5'),'#skF_3',B_390)
      | ~ r2_hidden(B_390,k1_tops_1('#skF_3','#skF_5'))
      | ~ m1_subset_1(B_390,u1_struct_0('#skF_3')) ) ),
    inference(splitRight,[status(thm)],[c_2447])).

tff(c_145,plain,(
    ! [A_106,B_107] :
      ( m1_subset_1(k1_tops_1(A_106,B_107),k1_zfmisc_1(u1_struct_0(A_106)))
      | ~ m1_subset_1(B_107,k1_zfmisc_1(u1_struct_0(A_106)))
      | ~ l1_pre_topc(A_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_42,plain,(
    ! [D_74] :
      ( ~ r1_tarski(D_74,'#skF_5')
      | ~ v3_pre_topc(D_74,'#skF_3')
      | ~ m1_connsp_2(D_74,'#skF_3','#skF_4')
      | ~ m1_subset_1(D_74,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v1_xboole_0(D_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_153,plain,(
    ! [B_107] :
      ( ~ r1_tarski(k1_tops_1('#skF_3',B_107),'#skF_5')
      | ~ v3_pre_topc(k1_tops_1('#skF_3',B_107),'#skF_3')
      | ~ m1_connsp_2(k1_tops_1('#skF_3',B_107),'#skF_3','#skF_4')
      | v1_xboole_0(k1_tops_1('#skF_3',B_107))
      | ~ m1_subset_1(B_107,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_145,c_42])).

tff(c_186,plain,(
    ! [B_115] :
      ( ~ r1_tarski(k1_tops_1('#skF_3',B_115),'#skF_5')
      | ~ v3_pre_topc(k1_tops_1('#skF_3',B_115),'#skF_3')
      | ~ m1_connsp_2(k1_tops_1('#skF_3',B_115),'#skF_3','#skF_4')
      | v1_xboole_0(k1_tops_1('#skF_3',B_115))
      | ~ m1_subset_1(B_115,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_153])).

tff(c_202,plain,
    ( ~ r1_tarski(k1_tops_1('#skF_3','#skF_5'),'#skF_5')
    | ~ v3_pre_topc(k1_tops_1('#skF_3','#skF_5'),'#skF_3')
    | ~ m1_connsp_2(k1_tops_1('#skF_3','#skF_5'),'#skF_3','#skF_4')
    | v1_xboole_0(k1_tops_1('#skF_3','#skF_5')) ),
    inference(resolution,[status(thm)],[c_46,c_186])).

tff(c_312,plain,
    ( ~ r1_tarski(k1_tops_1('#skF_3','#skF_5'),'#skF_5')
    | ~ m1_connsp_2(k1_tops_1('#skF_3','#skF_5'),'#skF_3','#skF_4')
    | v1_xboole_0(k1_tops_1('#skF_3','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_295,c_202])).

tff(c_313,plain,(
    ~ m1_connsp_2(k1_tops_1('#skF_3','#skF_5'),'#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_312])).

tff(c_2712,plain,
    ( ~ r2_hidden('#skF_4',k1_tops_1('#skF_3','#skF_5'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2700,c_313])).

tff(c_2723,plain,(
    ~ r2_hidden('#skF_4',k1_tops_1('#skF_3','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_2712])).

tff(c_2726,plain,
    ( ~ m1_connsp_2('#skF_5','#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_1806,c_2723])).

tff(c_2733,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_44,c_2726])).

tff(c_2734,plain,
    ( ~ r1_tarski(k1_tops_1('#skF_3','#skF_5'),'#skF_5')
    | v1_xboole_0(k1_tops_1('#skF_3','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_312])).

tff(c_2749,plain,(
    ~ r1_tarski(k1_tops_1('#skF_3','#skF_5'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_2734])).

tff(c_78,plain,(
    ! [A_82,B_83] :
      ( r2_hidden('#skF_1'(A_82,B_83),A_82)
      | r1_tarski(A_82,B_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_83,plain,(
    ! [A_82] : r1_tarski(A_82,A_82) ),
    inference(resolution,[status(thm)],[c_78,c_4])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_88,plain,(
    ! [C_85,B_86,A_87] :
      ( r2_hidden(C_85,B_86)
      | ~ r2_hidden(C_85,A_87)
      | ~ r1_tarski(A_87,B_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_91,plain,(
    ! [A_1,B_2,B_86] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_86)
      | ~ r1_tarski(A_1,B_86)
      | r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_88])).

tff(c_2735,plain,(
    m1_connsp_2(k1_tops_1('#skF_3','#skF_5'),'#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_312])).

tff(c_3246,plain,(
    ! [C_471,B_472,A_473] :
      ( r2_hidden(C_471,B_472)
      | ~ m1_connsp_2(B_472,A_473,C_471)
      | ~ m1_subset_1(C_471,u1_struct_0(A_473))
      | ~ m1_subset_1(B_472,k1_zfmisc_1(u1_struct_0(A_473)))
      | ~ l1_pre_topc(A_473)
      | ~ v2_pre_topc(A_473)
      | v2_struct_0(A_473) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_3248,plain,
    ( r2_hidden('#skF_4',k1_tops_1('#skF_3','#skF_5'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ m1_subset_1(k1_tops_1('#skF_3','#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_2735,c_3246])).

tff(c_3253,plain,
    ( r2_hidden('#skF_4',k1_tops_1('#skF_3','#skF_5'))
    | ~ m1_subset_1(k1_tops_1('#skF_3','#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_3248])).

tff(c_3254,plain,
    ( r2_hidden('#skF_4',k1_tops_1('#skF_3','#skF_5'))
    | ~ m1_subset_1(k1_tops_1('#skF_3','#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_3253])).

tff(c_3298,plain,(
    ~ m1_subset_1(k1_tops_1('#skF_3','#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_3254])).

tff(c_3382,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_3298])).

tff(c_3389,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_3382])).

tff(c_3391,plain,(
    m1_subset_1(k1_tops_1('#skF_3','#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_3254])).

tff(c_14,plain,(
    ! [A_12,C_14,B_13] :
      ( m1_subset_1(A_12,C_14)
      | ~ m1_subset_1(B_13,k1_zfmisc_1(C_14))
      | ~ r2_hidden(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_4248,plain,(
    ! [A_509] :
      ( m1_subset_1(A_509,u1_struct_0('#skF_3'))
      | ~ r2_hidden(A_509,k1_tops_1('#skF_3','#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_3391,c_14])).

tff(c_4278,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1('#skF_1'(A_1,B_2),u1_struct_0('#skF_3'))
      | ~ r1_tarski(A_1,k1_tops_1('#skF_3','#skF_5'))
      | r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_91,c_4248])).

tff(c_4279,plain,(
    ! [B_2] :
      ( m1_subset_1('#skF_1'(k1_tops_1('#skF_3','#skF_5'),B_2),u1_struct_0('#skF_3'))
      | r1_tarski(k1_tops_1('#skF_3','#skF_5'),B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_4248])).

tff(c_4769,plain,(
    ! [C_544,A_545,B_546] :
      ( m1_connsp_2(C_544,A_545,B_546)
      | ~ r2_hidden(B_546,k1_tops_1(A_545,C_544))
      | ~ m1_subset_1(C_544,k1_zfmisc_1(u1_struct_0(A_545)))
      | ~ m1_subset_1(B_546,u1_struct_0(A_545))
      | ~ l1_pre_topc(A_545)
      | ~ v2_pre_topc(A_545)
      | v2_struct_0(A_545) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_8558,plain,(
    ! [C_808,A_809,B_810] :
      ( m1_connsp_2(C_808,A_809,'#skF_1'(k1_tops_1(A_809,C_808),B_810))
      | ~ m1_subset_1(C_808,k1_zfmisc_1(u1_struct_0(A_809)))
      | ~ m1_subset_1('#skF_1'(k1_tops_1(A_809,C_808),B_810),u1_struct_0(A_809))
      | ~ l1_pre_topc(A_809)
      | ~ v2_pre_topc(A_809)
      | v2_struct_0(A_809)
      | r1_tarski(k1_tops_1(A_809,C_808),B_810) ) ),
    inference(resolution,[status(thm)],[c_6,c_4769])).

tff(c_8579,plain,(
    ! [B_2] :
      ( m1_connsp_2('#skF_5','#skF_3','#skF_1'(k1_tops_1('#skF_3','#skF_5'),B_2))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | r1_tarski(k1_tops_1('#skF_3','#skF_5'),B_2) ) ),
    inference(resolution,[status(thm)],[c_4279,c_8558])).

tff(c_8625,plain,(
    ! [B_2] :
      ( m1_connsp_2('#skF_5','#skF_3','#skF_1'(k1_tops_1('#skF_3','#skF_5'),B_2))
      | v2_struct_0('#skF_3')
      | r1_tarski(k1_tops_1('#skF_3','#skF_5'),B_2) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_46,c_8579])).

tff(c_8661,plain,(
    ! [B_813] :
      ( m1_connsp_2('#skF_5','#skF_3','#skF_1'(k1_tops_1('#skF_3','#skF_5'),B_813))
      | r1_tarski(k1_tops_1('#skF_3','#skF_5'),B_813) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_8625])).

tff(c_40,plain,(
    ! [C_62,B_60,A_56] :
      ( r2_hidden(C_62,B_60)
      | ~ m1_connsp_2(B_60,A_56,C_62)
      | ~ m1_subset_1(C_62,u1_struct_0(A_56))
      | ~ m1_subset_1(B_60,k1_zfmisc_1(u1_struct_0(A_56)))
      | ~ l1_pre_topc(A_56)
      | ~ v2_pre_topc(A_56)
      | v2_struct_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_8682,plain,(
    ! [B_813] :
      ( r2_hidden('#skF_1'(k1_tops_1('#skF_3','#skF_5'),B_813),'#skF_5')
      | ~ m1_subset_1('#skF_1'(k1_tops_1('#skF_3','#skF_5'),B_813),u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | r1_tarski(k1_tops_1('#skF_3','#skF_5'),B_813) ) ),
    inference(resolution,[status(thm)],[c_8661,c_40])).

tff(c_8695,plain,(
    ! [B_813] :
      ( r2_hidden('#skF_1'(k1_tops_1('#skF_3','#skF_5'),B_813),'#skF_5')
      | ~ m1_subset_1('#skF_1'(k1_tops_1('#skF_3','#skF_5'),B_813),u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3')
      | r1_tarski(k1_tops_1('#skF_3','#skF_5'),B_813) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_46,c_8682])).

tff(c_8697,plain,(
    ! [B_814] :
      ( r2_hidden('#skF_1'(k1_tops_1('#skF_3','#skF_5'),B_814),'#skF_5')
      | ~ m1_subset_1('#skF_1'(k1_tops_1('#skF_3','#skF_5'),B_814),u1_struct_0('#skF_3'))
      | r1_tarski(k1_tops_1('#skF_3','#skF_5'),B_814) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_8695])).

tff(c_8717,plain,(
    ! [B_2] :
      ( r2_hidden('#skF_1'(k1_tops_1('#skF_3','#skF_5'),B_2),'#skF_5')
      | ~ r1_tarski(k1_tops_1('#skF_3','#skF_5'),k1_tops_1('#skF_3','#skF_5'))
      | r1_tarski(k1_tops_1('#skF_3','#skF_5'),B_2) ) ),
    inference(resolution,[status(thm)],[c_4278,c_8697])).

tff(c_8759,plain,(
    ! [B_815] :
      ( r2_hidden('#skF_1'(k1_tops_1('#skF_3','#skF_5'),B_815),'#skF_5')
      | r1_tarski(k1_tops_1('#skF_3','#skF_5'),B_815) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_8717])).

tff(c_8771,plain,(
    r1_tarski(k1_tops_1('#skF_3','#skF_5'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_8759,c_4])).

tff(c_8779,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2749,c_2749,c_8771])).

tff(c_8780,plain,(
    v1_xboole_0(k1_tops_1('#skF_3','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_2734])).

tff(c_9112,plain,(
    ! [C_865,B_866,A_867] :
      ( r2_hidden(C_865,B_866)
      | ~ m1_connsp_2(B_866,A_867,C_865)
      | ~ m1_subset_1(C_865,u1_struct_0(A_867))
      | ~ m1_subset_1(B_866,k1_zfmisc_1(u1_struct_0(A_867)))
      | ~ l1_pre_topc(A_867)
      | ~ v2_pre_topc(A_867)
      | v2_struct_0(A_867) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_9114,plain,
    ( r2_hidden('#skF_4',k1_tops_1('#skF_3','#skF_5'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ m1_subset_1(k1_tops_1('#skF_3','#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_2735,c_9112])).

tff(c_9119,plain,
    ( r2_hidden('#skF_4',k1_tops_1('#skF_3','#skF_5'))
    | ~ m1_subset_1(k1_tops_1('#skF_3','#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_9114])).

tff(c_9120,plain,
    ( r2_hidden('#skF_4',k1_tops_1('#skF_3','#skF_5'))
    | ~ m1_subset_1(k1_tops_1('#skF_3','#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_9119])).

tff(c_9160,plain,(
    ~ m1_subset_1(k1_tops_1('#skF_3','#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_9120])).

tff(c_9210,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_9160])).

tff(c_9217,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_9210])).

tff(c_9218,plain,(
    r2_hidden('#skF_4',k1_tops_1('#skF_3','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_9120])).

tff(c_12,plain,(
    ! [A_10,B_11] :
      ( m1_subset_1(A_10,k1_zfmisc_1(B_11))
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_92,plain,(
    ! [C_88,B_89,A_90] :
      ( ~ v1_xboole_0(C_88)
      | ~ m1_subset_1(B_89,k1_zfmisc_1(C_88))
      | ~ r2_hidden(A_90,B_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_97,plain,(
    ! [B_11,A_90,A_10] :
      ( ~ v1_xboole_0(B_11)
      | ~ r2_hidden(A_90,A_10)
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(resolution,[status(thm)],[c_12,c_92])).

tff(c_9516,plain,(
    ! [B_881] :
      ( ~ v1_xboole_0(B_881)
      | ~ r1_tarski(k1_tops_1('#skF_3','#skF_5'),B_881) ) ),
    inference(resolution,[status(thm)],[c_9218,c_97])).

tff(c_9538,plain,(
    ~ v1_xboole_0(k1_tops_1('#skF_3','#skF_5')) ),
    inference(resolution,[status(thm)],[c_83,c_9516])).

tff(c_9553,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8780,c_9538])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:41:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.48/3.16  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.48/3.17  
% 9.48/3.17  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.48/3.17  %$ m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4 > #skF_1
% 9.48/3.17  
% 9.48/3.17  %Foreground sorts:
% 9.48/3.17  
% 9.48/3.17  
% 9.48/3.17  %Background operators:
% 9.48/3.17  
% 9.48/3.17  
% 9.48/3.17  %Foreground operators:
% 9.48/3.17  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 9.48/3.17  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 9.48/3.17  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 9.48/3.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.48/3.17  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.48/3.17  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 9.48/3.17  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.48/3.17  tff('#skF_5', type, '#skF_5': $i).
% 9.48/3.17  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 9.48/3.17  tff('#skF_3', type, '#skF_3': $i).
% 9.48/3.17  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 9.48/3.17  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.48/3.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.48/3.17  tff('#skF_4', type, '#skF_4': $i).
% 9.48/3.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.48/3.17  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 9.48/3.17  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 9.48/3.17  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 9.48/3.17  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 9.48/3.17  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.48/3.17  
% 9.72/3.20  tff(f_173, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(m1_connsp_2(C, A, B) & (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A)))) => ~((m1_connsp_2(D, A, B) & v3_pre_topc(D, A)) & r1_tarski(D, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_connsp_2)).
% 9.72/3.20  tff(f_126, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m1_connsp_2(C, A, B) <=> r2_hidden(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_connsp_2)).
% 9.72/3.20  tff(f_62, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k1_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tops_1)).
% 9.72/3.20  tff(f_70, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_tops_1)).
% 9.72/3.20  tff(f_109, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (l1_pre_topc(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => ((v3_pre_topc(D, B) => (k1_tops_1(B, D) = D)) & ((k1_tops_1(A, C) = C) => v3_pre_topc(C, A))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_tops_1)).
% 9.72/3.20  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 9.72/3.20  tff(f_143, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (m1_connsp_2(B, A, C) => r2_hidden(C, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_connsp_2)).
% 9.72/3.20  tff(f_49, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 9.72/3.20  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 9.72/3.20  tff(f_56, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 9.72/3.20  tff(c_48, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_173])).
% 9.72/3.20  tff(c_44, plain, (m1_connsp_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_173])).
% 9.72/3.20  tff(c_54, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_173])).
% 9.72/3.20  tff(c_52, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_173])).
% 9.72/3.20  tff(c_50, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_173])).
% 9.72/3.20  tff(c_46, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_173])).
% 9.72/3.20  tff(c_1782, plain, (![B_307, A_308, C_309]: (r2_hidden(B_307, k1_tops_1(A_308, C_309)) | ~m1_connsp_2(C_309, A_308, B_307) | ~m1_subset_1(C_309, k1_zfmisc_1(u1_struct_0(A_308))) | ~m1_subset_1(B_307, u1_struct_0(A_308)) | ~l1_pre_topc(A_308) | ~v2_pre_topc(A_308) | v2_struct_0(A_308))), inference(cnfTransformation, [status(thm)], [f_126])).
% 9.72/3.20  tff(c_1797, plain, (![B_307]: (r2_hidden(B_307, k1_tops_1('#skF_3', '#skF_5')) | ~m1_connsp_2('#skF_5', '#skF_3', B_307) | ~m1_subset_1(B_307, u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_46, c_1782])).
% 9.72/3.20  tff(c_1805, plain, (![B_307]: (r2_hidden(B_307, k1_tops_1('#skF_3', '#skF_5')) | ~m1_connsp_2('#skF_5', '#skF_3', B_307) | ~m1_subset_1(B_307, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_1797])).
% 9.72/3.20  tff(c_1806, plain, (![B_307]: (r2_hidden(B_307, k1_tops_1('#skF_3', '#skF_5')) | ~m1_connsp_2('#skF_5', '#skF_3', B_307) | ~m1_subset_1(B_307, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_54, c_1805])).
% 9.72/3.20  tff(c_18, plain, (![A_18, B_19]: (m1_subset_1(k1_tops_1(A_18, B_19), k1_zfmisc_1(u1_struct_0(A_18))) | ~m1_subset_1(B_19, k1_zfmisc_1(u1_struct_0(A_18))) | ~l1_pre_topc(A_18))), inference(cnfTransformation, [status(thm)], [f_62])).
% 9.72/3.20  tff(c_279, plain, (![A_133, B_134]: (v3_pre_topc(k1_tops_1(A_133, B_134), A_133) | ~m1_subset_1(B_134, k1_zfmisc_1(u1_struct_0(A_133))) | ~l1_pre_topc(A_133) | ~v2_pre_topc(A_133))), inference(cnfTransformation, [status(thm)], [f_70])).
% 9.72/3.20  tff(c_289, plain, (v3_pre_topc(k1_tops_1('#skF_3', '#skF_5'), '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_46, c_279])).
% 9.72/3.20  tff(c_295, plain, (v3_pre_topc(k1_tops_1('#skF_3', '#skF_5'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_289])).
% 9.72/3.20  tff(c_34, plain, (![B_42, D_48, C_46, A_34]: (k1_tops_1(B_42, D_48)=D_48 | ~v3_pre_topc(D_48, B_42) | ~m1_subset_1(D_48, k1_zfmisc_1(u1_struct_0(B_42))) | ~m1_subset_1(C_46, k1_zfmisc_1(u1_struct_0(A_34))) | ~l1_pre_topc(B_42) | ~l1_pre_topc(A_34) | ~v2_pre_topc(A_34))), inference(cnfTransformation, [status(thm)], [f_109])).
% 9.72/3.20  tff(c_1114, plain, (![C_250, A_251]: (~m1_subset_1(C_250, k1_zfmisc_1(u1_struct_0(A_251))) | ~l1_pre_topc(A_251) | ~v2_pre_topc(A_251))), inference(splitLeft, [status(thm)], [c_34])).
% 9.72/3.20  tff(c_1132, plain, (~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_46, c_1114])).
% 9.72/3.20  tff(c_1140, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_1132])).
% 9.72/3.20  tff(c_1226, plain, (![B_257, D_258]: (k1_tops_1(B_257, D_258)=D_258 | ~v3_pre_topc(D_258, B_257) | ~m1_subset_1(D_258, k1_zfmisc_1(u1_struct_0(B_257))) | ~l1_pre_topc(B_257))), inference(splitRight, [status(thm)], [c_34])).
% 9.72/3.20  tff(c_2387, plain, (![A_374, B_375]: (k1_tops_1(A_374, k1_tops_1(A_374, B_375))=k1_tops_1(A_374, B_375) | ~v3_pre_topc(k1_tops_1(A_374, B_375), A_374) | ~m1_subset_1(B_375, k1_zfmisc_1(u1_struct_0(A_374))) | ~l1_pre_topc(A_374))), inference(resolution, [status(thm)], [c_18, c_1226])).
% 9.72/3.20  tff(c_2396, plain, (k1_tops_1('#skF_3', k1_tops_1('#skF_3', '#skF_5'))=k1_tops_1('#skF_3', '#skF_5') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_295, c_2387])).
% 9.72/3.20  tff(c_2404, plain, (k1_tops_1('#skF_3', k1_tops_1('#skF_3', '#skF_5'))=k1_tops_1('#skF_3', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_46, c_2396])).
% 9.72/3.20  tff(c_36, plain, (![C_55, A_49, B_53]: (m1_connsp_2(C_55, A_49, B_53) | ~r2_hidden(B_53, k1_tops_1(A_49, C_55)) | ~m1_subset_1(C_55, k1_zfmisc_1(u1_struct_0(A_49))) | ~m1_subset_1(B_53, u1_struct_0(A_49)) | ~l1_pre_topc(A_49) | ~v2_pre_topc(A_49) | v2_struct_0(A_49))), inference(cnfTransformation, [status(thm)], [f_126])).
% 9.72/3.20  tff(c_2419, plain, (![B_53]: (m1_connsp_2(k1_tops_1('#skF_3', '#skF_5'), '#skF_3', B_53) | ~r2_hidden(B_53, k1_tops_1('#skF_3', '#skF_5')) | ~m1_subset_1(k1_tops_1('#skF_3', '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1(B_53, u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_2404, c_36])).
% 9.72/3.20  tff(c_2446, plain, (![B_53]: (m1_connsp_2(k1_tops_1('#skF_3', '#skF_5'), '#skF_3', B_53) | ~r2_hidden(B_53, k1_tops_1('#skF_3', '#skF_5')) | ~m1_subset_1(k1_tops_1('#skF_3', '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1(B_53, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_2419])).
% 9.72/3.20  tff(c_2447, plain, (![B_53]: (m1_connsp_2(k1_tops_1('#skF_3', '#skF_5'), '#skF_3', B_53) | ~r2_hidden(B_53, k1_tops_1('#skF_3', '#skF_5')) | ~m1_subset_1(k1_tops_1('#skF_3', '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1(B_53, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_54, c_2446])).
% 9.72/3.20  tff(c_2464, plain, (~m1_subset_1(k1_tops_1('#skF_3', '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(splitLeft, [status(thm)], [c_2447])).
% 9.72/3.20  tff(c_2467, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_18, c_2464])).
% 9.72/3.20  tff(c_2474, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_46, c_2467])).
% 9.72/3.20  tff(c_2700, plain, (![B_390]: (m1_connsp_2(k1_tops_1('#skF_3', '#skF_5'), '#skF_3', B_390) | ~r2_hidden(B_390, k1_tops_1('#skF_3', '#skF_5')) | ~m1_subset_1(B_390, u1_struct_0('#skF_3')))), inference(splitRight, [status(thm)], [c_2447])).
% 9.72/3.20  tff(c_145, plain, (![A_106, B_107]: (m1_subset_1(k1_tops_1(A_106, B_107), k1_zfmisc_1(u1_struct_0(A_106))) | ~m1_subset_1(B_107, k1_zfmisc_1(u1_struct_0(A_106))) | ~l1_pre_topc(A_106))), inference(cnfTransformation, [status(thm)], [f_62])).
% 9.72/3.20  tff(c_42, plain, (![D_74]: (~r1_tarski(D_74, '#skF_5') | ~v3_pre_topc(D_74, '#skF_3') | ~m1_connsp_2(D_74, '#skF_3', '#skF_4') | ~m1_subset_1(D_74, k1_zfmisc_1(u1_struct_0('#skF_3'))) | v1_xboole_0(D_74))), inference(cnfTransformation, [status(thm)], [f_173])).
% 9.72/3.20  tff(c_153, plain, (![B_107]: (~r1_tarski(k1_tops_1('#skF_3', B_107), '#skF_5') | ~v3_pre_topc(k1_tops_1('#skF_3', B_107), '#skF_3') | ~m1_connsp_2(k1_tops_1('#skF_3', B_107), '#skF_3', '#skF_4') | v1_xboole_0(k1_tops_1('#skF_3', B_107)) | ~m1_subset_1(B_107, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_145, c_42])).
% 9.72/3.20  tff(c_186, plain, (![B_115]: (~r1_tarski(k1_tops_1('#skF_3', B_115), '#skF_5') | ~v3_pre_topc(k1_tops_1('#skF_3', B_115), '#skF_3') | ~m1_connsp_2(k1_tops_1('#skF_3', B_115), '#skF_3', '#skF_4') | v1_xboole_0(k1_tops_1('#skF_3', B_115)) | ~m1_subset_1(B_115, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_153])).
% 9.72/3.20  tff(c_202, plain, (~r1_tarski(k1_tops_1('#skF_3', '#skF_5'), '#skF_5') | ~v3_pre_topc(k1_tops_1('#skF_3', '#skF_5'), '#skF_3') | ~m1_connsp_2(k1_tops_1('#skF_3', '#skF_5'), '#skF_3', '#skF_4') | v1_xboole_0(k1_tops_1('#skF_3', '#skF_5'))), inference(resolution, [status(thm)], [c_46, c_186])).
% 9.72/3.20  tff(c_312, plain, (~r1_tarski(k1_tops_1('#skF_3', '#skF_5'), '#skF_5') | ~m1_connsp_2(k1_tops_1('#skF_3', '#skF_5'), '#skF_3', '#skF_4') | v1_xboole_0(k1_tops_1('#skF_3', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_295, c_202])).
% 9.72/3.20  tff(c_313, plain, (~m1_connsp_2(k1_tops_1('#skF_3', '#skF_5'), '#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_312])).
% 9.72/3.20  tff(c_2712, plain, (~r2_hidden('#skF_4', k1_tops_1('#skF_3', '#skF_5')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_2700, c_313])).
% 9.72/3.20  tff(c_2723, plain, (~r2_hidden('#skF_4', k1_tops_1('#skF_3', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_2712])).
% 9.72/3.20  tff(c_2726, plain, (~m1_connsp_2('#skF_5', '#skF_3', '#skF_4') | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_1806, c_2723])).
% 9.72/3.20  tff(c_2733, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_44, c_2726])).
% 9.72/3.20  tff(c_2734, plain, (~r1_tarski(k1_tops_1('#skF_3', '#skF_5'), '#skF_5') | v1_xboole_0(k1_tops_1('#skF_3', '#skF_5'))), inference(splitRight, [status(thm)], [c_312])).
% 9.72/3.20  tff(c_2749, plain, (~r1_tarski(k1_tops_1('#skF_3', '#skF_5'), '#skF_5')), inference(splitLeft, [status(thm)], [c_2734])).
% 9.72/3.20  tff(c_78, plain, (![A_82, B_83]: (r2_hidden('#skF_1'(A_82, B_83), A_82) | r1_tarski(A_82, B_83))), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.72/3.20  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.72/3.20  tff(c_83, plain, (![A_82]: (r1_tarski(A_82, A_82))), inference(resolution, [status(thm)], [c_78, c_4])).
% 9.72/3.20  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.72/3.20  tff(c_88, plain, (![C_85, B_86, A_87]: (r2_hidden(C_85, B_86) | ~r2_hidden(C_85, A_87) | ~r1_tarski(A_87, B_86))), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.72/3.20  tff(c_91, plain, (![A_1, B_2, B_86]: (r2_hidden('#skF_1'(A_1, B_2), B_86) | ~r1_tarski(A_1, B_86) | r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_6, c_88])).
% 9.72/3.20  tff(c_2735, plain, (m1_connsp_2(k1_tops_1('#skF_3', '#skF_5'), '#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_312])).
% 9.72/3.20  tff(c_3246, plain, (![C_471, B_472, A_473]: (r2_hidden(C_471, B_472) | ~m1_connsp_2(B_472, A_473, C_471) | ~m1_subset_1(C_471, u1_struct_0(A_473)) | ~m1_subset_1(B_472, k1_zfmisc_1(u1_struct_0(A_473))) | ~l1_pre_topc(A_473) | ~v2_pre_topc(A_473) | v2_struct_0(A_473))), inference(cnfTransformation, [status(thm)], [f_143])).
% 9.72/3.20  tff(c_3248, plain, (r2_hidden('#skF_4', k1_tops_1('#skF_3', '#skF_5')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~m1_subset_1(k1_tops_1('#skF_3', '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_2735, c_3246])).
% 9.72/3.20  tff(c_3253, plain, (r2_hidden('#skF_4', k1_tops_1('#skF_3', '#skF_5')) | ~m1_subset_1(k1_tops_1('#skF_3', '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_3248])).
% 9.72/3.20  tff(c_3254, plain, (r2_hidden('#skF_4', k1_tops_1('#skF_3', '#skF_5')) | ~m1_subset_1(k1_tops_1('#skF_3', '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_54, c_3253])).
% 9.72/3.20  tff(c_3298, plain, (~m1_subset_1(k1_tops_1('#skF_3', '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(splitLeft, [status(thm)], [c_3254])).
% 9.72/3.20  tff(c_3382, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_18, c_3298])).
% 9.72/3.20  tff(c_3389, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_46, c_3382])).
% 9.72/3.20  tff(c_3391, plain, (m1_subset_1(k1_tops_1('#skF_3', '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(splitRight, [status(thm)], [c_3254])).
% 9.72/3.20  tff(c_14, plain, (![A_12, C_14, B_13]: (m1_subset_1(A_12, C_14) | ~m1_subset_1(B_13, k1_zfmisc_1(C_14)) | ~r2_hidden(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_49])).
% 9.72/3.20  tff(c_4248, plain, (![A_509]: (m1_subset_1(A_509, u1_struct_0('#skF_3')) | ~r2_hidden(A_509, k1_tops_1('#skF_3', '#skF_5')))), inference(resolution, [status(thm)], [c_3391, c_14])).
% 9.72/3.20  tff(c_4278, plain, (![A_1, B_2]: (m1_subset_1('#skF_1'(A_1, B_2), u1_struct_0('#skF_3')) | ~r1_tarski(A_1, k1_tops_1('#skF_3', '#skF_5')) | r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_91, c_4248])).
% 9.72/3.20  tff(c_4279, plain, (![B_2]: (m1_subset_1('#skF_1'(k1_tops_1('#skF_3', '#skF_5'), B_2), u1_struct_0('#skF_3')) | r1_tarski(k1_tops_1('#skF_3', '#skF_5'), B_2))), inference(resolution, [status(thm)], [c_6, c_4248])).
% 9.72/3.20  tff(c_4769, plain, (![C_544, A_545, B_546]: (m1_connsp_2(C_544, A_545, B_546) | ~r2_hidden(B_546, k1_tops_1(A_545, C_544)) | ~m1_subset_1(C_544, k1_zfmisc_1(u1_struct_0(A_545))) | ~m1_subset_1(B_546, u1_struct_0(A_545)) | ~l1_pre_topc(A_545) | ~v2_pre_topc(A_545) | v2_struct_0(A_545))), inference(cnfTransformation, [status(thm)], [f_126])).
% 9.72/3.20  tff(c_8558, plain, (![C_808, A_809, B_810]: (m1_connsp_2(C_808, A_809, '#skF_1'(k1_tops_1(A_809, C_808), B_810)) | ~m1_subset_1(C_808, k1_zfmisc_1(u1_struct_0(A_809))) | ~m1_subset_1('#skF_1'(k1_tops_1(A_809, C_808), B_810), u1_struct_0(A_809)) | ~l1_pre_topc(A_809) | ~v2_pre_topc(A_809) | v2_struct_0(A_809) | r1_tarski(k1_tops_1(A_809, C_808), B_810))), inference(resolution, [status(thm)], [c_6, c_4769])).
% 9.72/3.20  tff(c_8579, plain, (![B_2]: (m1_connsp_2('#skF_5', '#skF_3', '#skF_1'(k1_tops_1('#skF_3', '#skF_5'), B_2)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | r1_tarski(k1_tops_1('#skF_3', '#skF_5'), B_2))), inference(resolution, [status(thm)], [c_4279, c_8558])).
% 9.72/3.20  tff(c_8625, plain, (![B_2]: (m1_connsp_2('#skF_5', '#skF_3', '#skF_1'(k1_tops_1('#skF_3', '#skF_5'), B_2)) | v2_struct_0('#skF_3') | r1_tarski(k1_tops_1('#skF_3', '#skF_5'), B_2))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_46, c_8579])).
% 9.72/3.20  tff(c_8661, plain, (![B_813]: (m1_connsp_2('#skF_5', '#skF_3', '#skF_1'(k1_tops_1('#skF_3', '#skF_5'), B_813)) | r1_tarski(k1_tops_1('#skF_3', '#skF_5'), B_813))), inference(negUnitSimplification, [status(thm)], [c_54, c_8625])).
% 9.72/3.20  tff(c_40, plain, (![C_62, B_60, A_56]: (r2_hidden(C_62, B_60) | ~m1_connsp_2(B_60, A_56, C_62) | ~m1_subset_1(C_62, u1_struct_0(A_56)) | ~m1_subset_1(B_60, k1_zfmisc_1(u1_struct_0(A_56))) | ~l1_pre_topc(A_56) | ~v2_pre_topc(A_56) | v2_struct_0(A_56))), inference(cnfTransformation, [status(thm)], [f_143])).
% 9.72/3.20  tff(c_8682, plain, (![B_813]: (r2_hidden('#skF_1'(k1_tops_1('#skF_3', '#skF_5'), B_813), '#skF_5') | ~m1_subset_1('#skF_1'(k1_tops_1('#skF_3', '#skF_5'), B_813), u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | r1_tarski(k1_tops_1('#skF_3', '#skF_5'), B_813))), inference(resolution, [status(thm)], [c_8661, c_40])).
% 9.72/3.20  tff(c_8695, plain, (![B_813]: (r2_hidden('#skF_1'(k1_tops_1('#skF_3', '#skF_5'), B_813), '#skF_5') | ~m1_subset_1('#skF_1'(k1_tops_1('#skF_3', '#skF_5'), B_813), u1_struct_0('#skF_3')) | v2_struct_0('#skF_3') | r1_tarski(k1_tops_1('#skF_3', '#skF_5'), B_813))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_46, c_8682])).
% 9.72/3.20  tff(c_8697, plain, (![B_814]: (r2_hidden('#skF_1'(k1_tops_1('#skF_3', '#skF_5'), B_814), '#skF_5') | ~m1_subset_1('#skF_1'(k1_tops_1('#skF_3', '#skF_5'), B_814), u1_struct_0('#skF_3')) | r1_tarski(k1_tops_1('#skF_3', '#skF_5'), B_814))), inference(negUnitSimplification, [status(thm)], [c_54, c_8695])).
% 9.72/3.20  tff(c_8717, plain, (![B_2]: (r2_hidden('#skF_1'(k1_tops_1('#skF_3', '#skF_5'), B_2), '#skF_5') | ~r1_tarski(k1_tops_1('#skF_3', '#skF_5'), k1_tops_1('#skF_3', '#skF_5')) | r1_tarski(k1_tops_1('#skF_3', '#skF_5'), B_2))), inference(resolution, [status(thm)], [c_4278, c_8697])).
% 9.72/3.20  tff(c_8759, plain, (![B_815]: (r2_hidden('#skF_1'(k1_tops_1('#skF_3', '#skF_5'), B_815), '#skF_5') | r1_tarski(k1_tops_1('#skF_3', '#skF_5'), B_815))), inference(demodulation, [status(thm), theory('equality')], [c_83, c_8717])).
% 9.72/3.20  tff(c_8771, plain, (r1_tarski(k1_tops_1('#skF_3', '#skF_5'), '#skF_5')), inference(resolution, [status(thm)], [c_8759, c_4])).
% 9.72/3.20  tff(c_8779, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2749, c_2749, c_8771])).
% 9.72/3.20  tff(c_8780, plain, (v1_xboole_0(k1_tops_1('#skF_3', '#skF_5'))), inference(splitRight, [status(thm)], [c_2734])).
% 9.72/3.20  tff(c_9112, plain, (![C_865, B_866, A_867]: (r2_hidden(C_865, B_866) | ~m1_connsp_2(B_866, A_867, C_865) | ~m1_subset_1(C_865, u1_struct_0(A_867)) | ~m1_subset_1(B_866, k1_zfmisc_1(u1_struct_0(A_867))) | ~l1_pre_topc(A_867) | ~v2_pre_topc(A_867) | v2_struct_0(A_867))), inference(cnfTransformation, [status(thm)], [f_143])).
% 9.72/3.20  tff(c_9114, plain, (r2_hidden('#skF_4', k1_tops_1('#skF_3', '#skF_5')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~m1_subset_1(k1_tops_1('#skF_3', '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_2735, c_9112])).
% 9.72/3.20  tff(c_9119, plain, (r2_hidden('#skF_4', k1_tops_1('#skF_3', '#skF_5')) | ~m1_subset_1(k1_tops_1('#skF_3', '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_9114])).
% 9.72/3.20  tff(c_9120, plain, (r2_hidden('#skF_4', k1_tops_1('#skF_3', '#skF_5')) | ~m1_subset_1(k1_tops_1('#skF_3', '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_54, c_9119])).
% 9.72/3.20  tff(c_9160, plain, (~m1_subset_1(k1_tops_1('#skF_3', '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(splitLeft, [status(thm)], [c_9120])).
% 9.72/3.20  tff(c_9210, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_18, c_9160])).
% 9.72/3.20  tff(c_9217, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_46, c_9210])).
% 9.72/3.20  tff(c_9218, plain, (r2_hidden('#skF_4', k1_tops_1('#skF_3', '#skF_5'))), inference(splitRight, [status(thm)], [c_9120])).
% 9.72/3.20  tff(c_12, plain, (![A_10, B_11]: (m1_subset_1(A_10, k1_zfmisc_1(B_11)) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_43])).
% 9.72/3.20  tff(c_92, plain, (![C_88, B_89, A_90]: (~v1_xboole_0(C_88) | ~m1_subset_1(B_89, k1_zfmisc_1(C_88)) | ~r2_hidden(A_90, B_89))), inference(cnfTransformation, [status(thm)], [f_56])).
% 9.72/3.20  tff(c_97, plain, (![B_11, A_90, A_10]: (~v1_xboole_0(B_11) | ~r2_hidden(A_90, A_10) | ~r1_tarski(A_10, B_11))), inference(resolution, [status(thm)], [c_12, c_92])).
% 9.72/3.20  tff(c_9516, plain, (![B_881]: (~v1_xboole_0(B_881) | ~r1_tarski(k1_tops_1('#skF_3', '#skF_5'), B_881))), inference(resolution, [status(thm)], [c_9218, c_97])).
% 9.72/3.20  tff(c_9538, plain, (~v1_xboole_0(k1_tops_1('#skF_3', '#skF_5'))), inference(resolution, [status(thm)], [c_83, c_9516])).
% 9.72/3.20  tff(c_9553, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8780, c_9538])).
% 9.72/3.20  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.72/3.20  
% 9.72/3.20  Inference rules
% 9.72/3.20  ----------------------
% 9.72/3.20  #Ref     : 0
% 9.72/3.20  #Sup     : 2182
% 9.72/3.20  #Fact    : 0
% 9.72/3.20  #Define  : 0
% 9.72/3.20  #Split   : 33
% 9.72/3.20  #Chain   : 0
% 9.72/3.20  #Close   : 0
% 9.72/3.20  
% 9.72/3.20  Ordering : KBO
% 9.72/3.20  
% 9.72/3.20  Simplification rules
% 9.72/3.20  ----------------------
% 9.72/3.20  #Subsume      : 804
% 9.72/3.20  #Demod        : 978
% 9.72/3.20  #Tautology    : 278
% 9.72/3.20  #SimpNegUnit  : 58
% 9.72/3.20  #BackRed      : 3
% 9.72/3.20  
% 9.72/3.20  #Partial instantiations: 0
% 9.72/3.20  #Strategies tried      : 1
% 9.72/3.20  
% 9.72/3.20  Timing (in seconds)
% 9.72/3.20  ----------------------
% 9.72/3.20  Preprocessing        : 0.35
% 9.72/3.20  Parsing              : 0.19
% 9.72/3.20  CNF conversion       : 0.03
% 9.72/3.20  Main loop            : 2.08
% 9.72/3.20  Inferencing          : 0.63
% 9.72/3.20  Reduction            : 0.60
% 9.72/3.20  Demodulation         : 0.40
% 9.72/3.20  BG Simplification    : 0.07
% 9.72/3.20  Subsumption          : 0.62
% 9.72/3.20  Abstraction          : 0.08
% 9.72/3.20  MUC search           : 0.00
% 9.72/3.20  Cooper               : 0.00
% 9.72/3.20  Total                : 2.48
% 9.72/3.20  Index Insertion      : 0.00
% 9.72/3.20  Index Deletion       : 0.00
% 9.72/3.20  Index Matching       : 0.00
% 9.72/3.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
