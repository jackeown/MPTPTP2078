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
% DateTime   : Thu Dec  3 10:24:13 EST 2020

% Result     : Theorem 7.51s
% Output     : CNFRefutation 7.51s
% Verified   : 
% Statistics : Number of formulae       :  157 ( 426 expanded)
%              Number of leaves         :   30 ( 159 expanded)
%              Depth                    :   14
%              Number of atoms          :  424 (1710 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_8 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(m1_connsp_2,type,(
    m1_connsp_2: ( $i * $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_141,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( m1_connsp_2(C,A,B)
                <=> ? [D] :
                      ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                      & v3_pre_topc(D,A)
                      & r1_tarski(D,C)
                      & r2_hidden(B,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_connsp_2)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

tff(f_64,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( v3_pre_topc(B,A)
                  & r1_tarski(B,C) )
               => r1_tarski(B,k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_tops_1)).

tff(f_50,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_85,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_pre_topc(B,A)
          <=> ! [C] :
                ( r2_hidden(C,B)
              <=> ? [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                    & v3_pre_topc(D,A)
                    & r1_tarski(D,B)
                    & r2_hidden(C,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_tops_1)).

tff(f_102,axiom,(
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

tff(c_52,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_70,plain,
    ( m1_connsp_2('#skF_7','#skF_5','#skF_6')
    | r1_tarski('#skF_8','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_90,plain,(
    r1_tarski('#skF_8','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_50,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_81,plain,(
    ! [A_90,B_91] :
      ( r1_tarski(A_90,B_91)
      | ~ m1_subset_1(A_90,k1_zfmisc_1(B_91)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_89,plain,(
    r1_tarski('#skF_7',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_50,c_81])).

tff(c_2380,plain,(
    ! [A_259,C_260,B_261] :
      ( r1_tarski(A_259,C_260)
      | ~ r1_tarski(B_261,C_260)
      | ~ r1_tarski(A_259,B_261) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2391,plain,(
    ! [A_263] :
      ( r1_tarski(A_263,u1_struct_0('#skF_5'))
      | ~ r1_tarski(A_263,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_89,c_2380])).

tff(c_6,plain,(
    ! [A_4,B_5] :
      ( m1_subset_1(A_4,k1_zfmisc_1(B_5))
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_74,plain,
    ( m1_connsp_2('#skF_7','#skF_5','#skF_6')
    | v3_pre_topc('#skF_8','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_91,plain,(
    v3_pre_topc('#skF_8','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_66,plain,
    ( m1_connsp_2('#skF_7','#skF_5','#skF_6')
    | r2_hidden('#skF_6','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_80,plain,(
    r2_hidden('#skF_6','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_78,plain,
    ( m1_connsp_2('#skF_7','#skF_5','#skF_6')
    | m1_subset_1('#skF_8',k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_92,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_78])).

tff(c_58,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_60,plain,(
    ! [D_87] :
      ( ~ r2_hidden('#skF_6',D_87)
      | ~ r1_tarski(D_87,'#skF_7')
      | ~ v3_pre_topc(D_87,'#skF_5')
      | ~ m1_subset_1(D_87,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_connsp_2('#skF_7','#skF_5','#skF_6') ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_297,plain,(
    ~ m1_connsp_2('#skF_7','#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_56,plain,(
    v2_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_54,plain,(
    l1_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_214,plain,(
    ! [A_106,B_107] :
      ( v3_pre_topc(k1_tops_1(A_106,B_107),A_106)
      | ~ m1_subset_1(B_107,k1_zfmisc_1(u1_struct_0(A_106)))
      | ~ l1_pre_topc(A_106)
      | ~ v2_pre_topc(A_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_221,plain,
    ( v3_pre_topc(k1_tops_1('#skF_5','#skF_7'),'#skF_5')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_214])).

tff(c_228,plain,(
    v3_pre_topc(k1_tops_1('#skF_5','#skF_7'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_221])).

tff(c_765,plain,(
    ! [B_200,A_201,C_202] :
      ( r1_tarski(B_200,k1_tops_1(A_201,C_202))
      | ~ r1_tarski(B_200,C_202)
      | ~ v3_pre_topc(B_200,A_201)
      | ~ m1_subset_1(C_202,k1_zfmisc_1(u1_struct_0(A_201)))
      | ~ m1_subset_1(B_200,k1_zfmisc_1(u1_struct_0(A_201)))
      | ~ l1_pre_topc(A_201) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_774,plain,(
    ! [B_200] :
      ( r1_tarski(B_200,k1_tops_1('#skF_5','#skF_7'))
      | ~ r1_tarski(B_200,'#skF_7')
      | ~ v3_pre_topc(B_200,'#skF_5')
      | ~ m1_subset_1(B_200,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_50,c_765])).

tff(c_783,plain,(
    ! [B_203] :
      ( r1_tarski(B_203,k1_tops_1('#skF_5','#skF_7'))
      | ~ r1_tarski(B_203,'#skF_7')
      | ~ v3_pre_topc(B_203,'#skF_5')
      | ~ m1_subset_1(B_203,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_774])).

tff(c_790,plain,
    ( r1_tarski('#skF_8',k1_tops_1('#skF_5','#skF_7'))
    | ~ r1_tarski('#skF_8','#skF_7')
    | ~ v3_pre_topc('#skF_8','#skF_5') ),
    inference(resolution,[status(thm)],[c_92,c_783])).

tff(c_803,plain,(
    r1_tarski('#skF_8',k1_tops_1('#skF_5','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_90,c_790])).

tff(c_142,plain,(
    ! [A_100,B_101] :
      ( r1_tarski(k1_tops_1(A_100,B_101),B_101)
      | ~ m1_subset_1(B_101,k1_zfmisc_1(u1_struct_0(A_100)))
      | ~ l1_pre_topc(A_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_149,plain,
    ( r1_tarski(k1_tops_1('#skF_5','#skF_7'),'#skF_7')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_142])).

tff(c_156,plain,(
    r1_tarski(k1_tops_1('#skF_5','#skF_7'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_149])).

tff(c_97,plain,(
    ! [A_92,C_93,B_94] :
      ( r1_tarski(A_92,C_93)
      | ~ r1_tarski(B_94,C_93)
      | ~ r1_tarski(A_92,B_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_105,plain,(
    ! [A_92] :
      ( r1_tarski(A_92,u1_struct_0('#skF_5'))
      | ~ r1_tarski(A_92,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_89,c_97])).

tff(c_769,plain,(
    ! [B_200] :
      ( r1_tarski(B_200,k1_tops_1('#skF_5','#skF_8'))
      | ~ r1_tarski(B_200,'#skF_8')
      | ~ v3_pre_topc(B_200,'#skF_5')
      | ~ m1_subset_1(B_200,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_92,c_765])).

tff(c_1013,plain,(
    ! [B_208] :
      ( r1_tarski(B_208,k1_tops_1('#skF_5','#skF_8'))
      | ~ r1_tarski(B_208,'#skF_8')
      | ~ v3_pre_topc(B_208,'#skF_5')
      | ~ m1_subset_1(B_208,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_769])).

tff(c_1036,plain,(
    ! [A_209] :
      ( r1_tarski(A_209,k1_tops_1('#skF_5','#skF_8'))
      | ~ r1_tarski(A_209,'#skF_8')
      | ~ v3_pre_topc(A_209,'#skF_5')
      | ~ r1_tarski(A_209,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_6,c_1013])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(B_2,C_3)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1759,plain,(
    ! [A_237,A_238] :
      ( r1_tarski(A_237,k1_tops_1('#skF_5','#skF_8'))
      | ~ r1_tarski(A_237,A_238)
      | ~ r1_tarski(A_238,'#skF_8')
      | ~ v3_pre_topc(A_238,'#skF_5')
      | ~ r1_tarski(A_238,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_1036,c_2])).

tff(c_1783,plain,
    ( r1_tarski('#skF_8',k1_tops_1('#skF_5','#skF_8'))
    | ~ r1_tarski(k1_tops_1('#skF_5','#skF_7'),'#skF_8')
    | ~ v3_pre_topc(k1_tops_1('#skF_5','#skF_7'),'#skF_5')
    | ~ r1_tarski(k1_tops_1('#skF_5','#skF_7'),u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_803,c_1759])).

tff(c_1869,plain,
    ( r1_tarski('#skF_8',k1_tops_1('#skF_5','#skF_8'))
    | ~ r1_tarski(k1_tops_1('#skF_5','#skF_7'),'#skF_8')
    | ~ r1_tarski(k1_tops_1('#skF_5','#skF_7'),u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_228,c_1783])).

tff(c_1966,plain,(
    ~ r1_tarski(k1_tops_1('#skF_5','#skF_7'),u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_1869])).

tff(c_1978,plain,(
    ~ r1_tarski(k1_tops_1('#skF_5','#skF_7'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_105,c_1966])).

tff(c_1989,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_1978])).

tff(c_1991,plain,(
    r1_tarski(k1_tops_1('#skF_5','#skF_7'),u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_1869])).

tff(c_2098,plain,(
    ! [C_244,B_245,D_246,A_247] :
      ( r2_hidden(C_244,B_245)
      | ~ r2_hidden(C_244,D_246)
      | ~ r1_tarski(D_246,B_245)
      | ~ v3_pre_topc(D_246,A_247)
      | ~ m1_subset_1(D_246,k1_zfmisc_1(u1_struct_0(A_247)))
      | ~ v3_pre_topc(B_245,A_247)
      | ~ m1_subset_1(B_245,k1_zfmisc_1(u1_struct_0(A_247)))
      | ~ l1_pre_topc(A_247)
      | ~ v2_pre_topc(A_247) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_2220,plain,(
    ! [B_252,A_253] :
      ( r2_hidden('#skF_6',B_252)
      | ~ r1_tarski('#skF_8',B_252)
      | ~ v3_pre_topc('#skF_8',A_253)
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(u1_struct_0(A_253)))
      | ~ v3_pre_topc(B_252,A_253)
      | ~ m1_subset_1(B_252,k1_zfmisc_1(u1_struct_0(A_253)))
      | ~ l1_pre_topc(A_253)
      | ~ v2_pre_topc(A_253) ) ),
    inference(resolution,[status(thm)],[c_80,c_2098])).

tff(c_2222,plain,(
    ! [B_252] :
      ( r2_hidden('#skF_6',B_252)
      | ~ r1_tarski('#skF_8',B_252)
      | ~ v3_pre_topc('#skF_8','#skF_5')
      | ~ v3_pre_topc(B_252,'#skF_5')
      | ~ m1_subset_1(B_252,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_92,c_2220])).

tff(c_2230,plain,(
    ! [B_254] :
      ( r2_hidden('#skF_6',B_254)
      | ~ r1_tarski('#skF_8',B_254)
      | ~ v3_pre_topc(B_254,'#skF_5')
      | ~ m1_subset_1(B_254,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_91,c_2222])).

tff(c_2262,plain,(
    ! [A_255] :
      ( r2_hidden('#skF_6',A_255)
      | ~ r1_tarski('#skF_8',A_255)
      | ~ v3_pre_topc(A_255,'#skF_5')
      | ~ r1_tarski(A_255,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_6,c_2230])).

tff(c_2268,plain,
    ( r2_hidden('#skF_6',k1_tops_1('#skF_5','#skF_7'))
    | ~ r1_tarski('#skF_8',k1_tops_1('#skF_5','#skF_7'))
    | ~ v3_pre_topc(k1_tops_1('#skF_5','#skF_7'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_1991,c_2262])).

tff(c_2321,plain,(
    r2_hidden('#skF_6',k1_tops_1('#skF_5','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_228,c_803,c_2268])).

tff(c_44,plain,(
    ! [C_64,A_58,B_62] :
      ( m1_connsp_2(C_64,A_58,B_62)
      | ~ r2_hidden(B_62,k1_tops_1(A_58,C_64))
      | ~ m1_subset_1(C_64,k1_zfmisc_1(u1_struct_0(A_58)))
      | ~ m1_subset_1(B_62,u1_struct_0(A_58))
      | ~ l1_pre_topc(A_58)
      | ~ v2_pre_topc(A_58)
      | v2_struct_0(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_2348,plain,
    ( m1_connsp_2('#skF_7','#skF_5','#skF_6')
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_2321,c_44])).

tff(c_2352,plain,
    ( m1_connsp_2('#skF_7','#skF_5','#skF_6')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_50,c_2348])).

tff(c_2354,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_297,c_2352])).

tff(c_2358,plain,(
    ! [D_258] :
      ( ~ r2_hidden('#skF_6',D_258)
      | ~ r1_tarski(D_258,'#skF_7')
      | ~ v3_pre_topc(D_258,'#skF_5')
      | ~ m1_subset_1(D_258,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_2361,plain,
    ( ~ r2_hidden('#skF_6','#skF_8')
    | ~ r1_tarski('#skF_8','#skF_7')
    | ~ v3_pre_topc('#skF_8','#skF_5') ),
    inference(resolution,[status(thm)],[c_92,c_2358])).

tff(c_2372,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_90,c_80,c_2361])).

tff(c_2374,plain,(
    ~ m1_subset_1('#skF_8',k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_2378,plain,(
    ~ r1_tarski('#skF_8',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_6,c_2374])).

tff(c_2396,plain,(
    ~ r1_tarski('#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_2391,c_2378])).

tff(c_2401,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_2396])).

tff(c_2402,plain,(
    m1_connsp_2('#skF_7','#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_2447,plain,(
    ! [A_272,B_273] :
      ( r1_tarski(k1_tops_1(A_272,B_273),B_273)
      | ~ m1_subset_1(B_273,k1_zfmisc_1(u1_struct_0(A_272)))
      | ~ l1_pre_topc(A_272) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_2452,plain,
    ( r1_tarski(k1_tops_1('#skF_5','#skF_7'),'#skF_7')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_2447])).

tff(c_2456,plain,(
    r1_tarski(k1_tops_1('#skF_5','#skF_7'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_2452])).

tff(c_3297,plain,(
    ! [B_389,A_390,C_391] :
      ( r2_hidden(B_389,k1_tops_1(A_390,C_391))
      | ~ m1_connsp_2(C_391,A_390,B_389)
      | ~ m1_subset_1(C_391,k1_zfmisc_1(u1_struct_0(A_390)))
      | ~ m1_subset_1(B_389,u1_struct_0(A_390))
      | ~ l1_pre_topc(A_390)
      | ~ v2_pre_topc(A_390)
      | v2_struct_0(A_390) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_3306,plain,(
    ! [B_389] :
      ( r2_hidden(B_389,k1_tops_1('#skF_5','#skF_7'))
      | ~ m1_connsp_2('#skF_7','#skF_5',B_389)
      | ~ m1_subset_1(B_389,u1_struct_0('#skF_5'))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_50,c_3297])).

tff(c_3312,plain,(
    ! [B_389] :
      ( r2_hidden(B_389,k1_tops_1('#skF_5','#skF_7'))
      | ~ m1_connsp_2('#skF_7','#skF_5',B_389)
      | ~ m1_subset_1(B_389,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_3306])).

tff(c_3314,plain,(
    ! [B_392] :
      ( r2_hidden(B_392,k1_tops_1('#skF_5','#skF_7'))
      | ~ m1_connsp_2('#skF_7','#skF_5',B_392)
      | ~ m1_subset_1(B_392,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_3312])).

tff(c_2488,plain,(
    ! [A_277,B_278] :
      ( v3_pre_topc(k1_tops_1(A_277,B_278),A_277)
      | ~ m1_subset_1(B_278,k1_zfmisc_1(u1_struct_0(A_277)))
      | ~ l1_pre_topc(A_277)
      | ~ v2_pre_topc(A_277) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2494,plain,(
    ! [A_277,A_4] :
      ( v3_pre_topc(k1_tops_1(A_277,A_4),A_277)
      | ~ l1_pre_topc(A_277)
      | ~ v2_pre_topc(A_277)
      | ~ r1_tarski(A_4,u1_struct_0(A_277)) ) ),
    inference(resolution,[status(thm)],[c_6,c_2488])).

tff(c_2405,plain,(
    ! [A_264,C_265,B_266] :
      ( r1_tarski(A_264,C_265)
      | ~ r1_tarski(B_266,C_265)
      | ~ r1_tarski(A_264,B_266) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2410,plain,(
    ! [A_264] :
      ( r1_tarski(A_264,u1_struct_0('#skF_5'))
      | ~ r1_tarski(A_264,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_89,c_2405])).

tff(c_2403,plain,(
    ~ v3_pre_topc('#skF_8','#skF_5') ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_72,plain,(
    ! [D_87] :
      ( ~ r2_hidden('#skF_6',D_87)
      | ~ r1_tarski(D_87,'#skF_7')
      | ~ v3_pre_topc(D_87,'#skF_5')
      | ~ m1_subset_1(D_87,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | v3_pre_topc('#skF_8','#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_2421,plain,(
    ! [D_269] :
      ( ~ r2_hidden('#skF_6',D_269)
      | ~ r1_tarski(D_269,'#skF_7')
      | ~ v3_pre_topc(D_269,'#skF_5')
      | ~ m1_subset_1(D_269,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_2403,c_72])).

tff(c_2515,plain,(
    ! [A_283] :
      ( ~ r2_hidden('#skF_6',A_283)
      | ~ r1_tarski(A_283,'#skF_7')
      | ~ v3_pre_topc(A_283,'#skF_5')
      | ~ r1_tarski(A_283,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_6,c_2421])).

tff(c_2529,plain,(
    ! [A_284] :
      ( ~ r2_hidden('#skF_6',A_284)
      | ~ v3_pre_topc(A_284,'#skF_5')
      | ~ r1_tarski(A_284,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_2410,c_2515])).

tff(c_2533,plain,(
    ! [A_4] :
      ( ~ r2_hidden('#skF_6',k1_tops_1('#skF_5',A_4))
      | ~ r1_tarski(k1_tops_1('#skF_5',A_4),'#skF_7')
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | ~ r1_tarski(A_4,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_2494,c_2529])).

tff(c_2539,plain,(
    ! [A_4] :
      ( ~ r2_hidden('#skF_6',k1_tops_1('#skF_5',A_4))
      | ~ r1_tarski(k1_tops_1('#skF_5',A_4),'#skF_7')
      | ~ r1_tarski(A_4,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_2533])).

tff(c_3321,plain,
    ( ~ r1_tarski(k1_tops_1('#skF_5','#skF_7'),'#skF_7')
    | ~ r1_tarski('#skF_7',u1_struct_0('#skF_5'))
    | ~ m1_connsp_2('#skF_7','#skF_5','#skF_6')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_3314,c_2539])).

tff(c_3329,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_2402,c_89,c_2456,c_3321])).

tff(c_3330,plain,(
    m1_connsp_2('#skF_7','#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_3350,plain,(
    ! [A_399,B_400] :
      ( r1_tarski(k1_tops_1(A_399,B_400),B_400)
      | ~ m1_subset_1(B_400,k1_zfmisc_1(u1_struct_0(A_399)))
      | ~ l1_pre_topc(A_399) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_3355,plain,
    ( r1_tarski(k1_tops_1('#skF_5','#skF_7'),'#skF_7')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_3350])).

tff(c_3359,plain,(
    r1_tarski(k1_tops_1('#skF_5','#skF_7'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_3355])).

tff(c_4708,plain,(
    ! [B_622,A_623,C_624] :
      ( r2_hidden(B_622,k1_tops_1(A_623,C_624))
      | ~ m1_connsp_2(C_624,A_623,B_622)
      | ~ m1_subset_1(C_624,k1_zfmisc_1(u1_struct_0(A_623)))
      | ~ m1_subset_1(B_622,u1_struct_0(A_623))
      | ~ l1_pre_topc(A_623)
      | ~ v2_pre_topc(A_623)
      | v2_struct_0(A_623) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_4717,plain,(
    ! [B_622] :
      ( r2_hidden(B_622,k1_tops_1('#skF_5','#skF_7'))
      | ~ m1_connsp_2('#skF_7','#skF_5',B_622)
      | ~ m1_subset_1(B_622,u1_struct_0('#skF_5'))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_50,c_4708])).

tff(c_4723,plain,(
    ! [B_622] :
      ( r2_hidden(B_622,k1_tops_1('#skF_5','#skF_7'))
      | ~ m1_connsp_2('#skF_7','#skF_5',B_622)
      | ~ m1_subset_1(B_622,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_4717])).

tff(c_4725,plain,(
    ! [B_625] :
      ( r2_hidden(B_625,k1_tops_1('#skF_5','#skF_7'))
      | ~ m1_connsp_2('#skF_7','#skF_5',B_625)
      | ~ m1_subset_1(B_625,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_4723])).

tff(c_4030,plain,(
    ! [A_512,B_513] :
      ( v3_pre_topc(k1_tops_1(A_512,B_513),A_512)
      | ~ m1_subset_1(B_513,k1_zfmisc_1(u1_struct_0(A_512)))
      | ~ l1_pre_topc(A_512)
      | ~ v2_pre_topc(A_512) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_4036,plain,(
    ! [A_512,A_4] :
      ( v3_pre_topc(k1_tops_1(A_512,A_4),A_512)
      | ~ l1_pre_topc(A_512)
      | ~ v2_pre_topc(A_512)
      | ~ r1_tarski(A_4,u1_struct_0(A_512)) ) ),
    inference(resolution,[status(thm)],[c_6,c_4030])).

tff(c_3334,plain,(
    ! [A_393,C_394,B_395] :
      ( r1_tarski(A_393,C_394)
      | ~ r1_tarski(B_395,C_394)
      | ~ r1_tarski(A_393,B_395) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_3337,plain,(
    ! [A_393] :
      ( r1_tarski(A_393,u1_struct_0('#skF_5'))
      | ~ r1_tarski(A_393,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_89,c_3334])).

tff(c_3331,plain,(
    ~ r1_tarski('#skF_8','#skF_7') ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_68,plain,(
    ! [D_87] :
      ( ~ r2_hidden('#skF_6',D_87)
      | ~ r1_tarski(D_87,'#skF_7')
      | ~ v3_pre_topc(D_87,'#skF_5')
      | ~ m1_subset_1(D_87,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | r1_tarski('#skF_8','#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_4041,plain,(
    ! [D_514] :
      ( ~ r2_hidden('#skF_6',D_514)
      | ~ r1_tarski(D_514,'#skF_7')
      | ~ v3_pre_topc(D_514,'#skF_5')
      | ~ m1_subset_1(D_514,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_3331,c_68])).

tff(c_4052,plain,(
    ! [A_517] :
      ( ~ r2_hidden('#skF_6',A_517)
      | ~ r1_tarski(A_517,'#skF_7')
      | ~ v3_pre_topc(A_517,'#skF_5')
      | ~ r1_tarski(A_517,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_6,c_4041])).

tff(c_4068,plain,(
    ! [A_518] :
      ( ~ r2_hidden('#skF_6',A_518)
      | ~ v3_pre_topc(A_518,'#skF_5')
      | ~ r1_tarski(A_518,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_3337,c_4052])).

tff(c_4072,plain,(
    ! [A_4] :
      ( ~ r2_hidden('#skF_6',k1_tops_1('#skF_5',A_4))
      | ~ r1_tarski(k1_tops_1('#skF_5',A_4),'#skF_7')
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | ~ r1_tarski(A_4,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_4036,c_4068])).

tff(c_4081,plain,(
    ! [A_4] :
      ( ~ r2_hidden('#skF_6',k1_tops_1('#skF_5',A_4))
      | ~ r1_tarski(k1_tops_1('#skF_5',A_4),'#skF_7')
      | ~ r1_tarski(A_4,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_4072])).

tff(c_4734,plain,
    ( ~ r1_tarski(k1_tops_1('#skF_5','#skF_7'),'#skF_7')
    | ~ r1_tarski('#skF_7',u1_struct_0('#skF_5'))
    | ~ m1_connsp_2('#skF_7','#skF_5','#skF_6')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_4725,c_4081])).

tff(c_4746,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_3330,c_89,c_3359,c_4734])).

tff(c_4747,plain,(
    m1_connsp_2('#skF_7','#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_4751,plain,(
    ! [A_626,B_627] :
      ( r1_tarski(A_626,B_627)
      | ~ m1_subset_1(A_626,k1_zfmisc_1(B_627)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_4759,plain,(
    r1_tarski('#skF_7',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_50,c_4751])).

tff(c_4807,plain,(
    ! [A_637,B_638] :
      ( r1_tarski(k1_tops_1(A_637,B_638),B_638)
      | ~ m1_subset_1(B_638,k1_zfmisc_1(u1_struct_0(A_637)))
      | ~ l1_pre_topc(A_637) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_4812,plain,
    ( r1_tarski(k1_tops_1('#skF_5','#skF_7'),'#skF_7')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_4807])).

tff(c_4816,plain,(
    r1_tarski(k1_tops_1('#skF_5','#skF_7'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_4812])).

tff(c_5652,plain,(
    ! [B_751,A_752,C_753] :
      ( r2_hidden(B_751,k1_tops_1(A_752,C_753))
      | ~ m1_connsp_2(C_753,A_752,B_751)
      | ~ m1_subset_1(C_753,k1_zfmisc_1(u1_struct_0(A_752)))
      | ~ m1_subset_1(B_751,u1_struct_0(A_752))
      | ~ l1_pre_topc(A_752)
      | ~ v2_pre_topc(A_752)
      | v2_struct_0(A_752) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_5661,plain,(
    ! [B_751] :
      ( r2_hidden(B_751,k1_tops_1('#skF_5','#skF_7'))
      | ~ m1_connsp_2('#skF_7','#skF_5',B_751)
      | ~ m1_subset_1(B_751,u1_struct_0('#skF_5'))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_50,c_5652])).

tff(c_5667,plain,(
    ! [B_751] :
      ( r2_hidden(B_751,k1_tops_1('#skF_5','#skF_7'))
      | ~ m1_connsp_2('#skF_7','#skF_5',B_751)
      | ~ m1_subset_1(B_751,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_5661])).

tff(c_5669,plain,(
    ! [B_754] :
      ( r2_hidden(B_754,k1_tops_1('#skF_5','#skF_7'))
      | ~ m1_connsp_2('#skF_7','#skF_5',B_754)
      | ~ m1_subset_1(B_754,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_5667])).

tff(c_4873,plain,(
    ! [A_645,B_646] :
      ( v3_pre_topc(k1_tops_1(A_645,B_646),A_645)
      | ~ m1_subset_1(B_646,k1_zfmisc_1(u1_struct_0(A_645)))
      | ~ l1_pre_topc(A_645)
      | ~ v2_pre_topc(A_645) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_4889,plain,(
    ! [A_647,A_648] :
      ( v3_pre_topc(k1_tops_1(A_647,A_648),A_647)
      | ~ l1_pre_topc(A_647)
      | ~ v2_pre_topc(A_647)
      | ~ r1_tarski(A_648,u1_struct_0(A_647)) ) ),
    inference(resolution,[status(thm)],[c_6,c_4873])).

tff(c_4760,plain,(
    ! [A_628,C_629,B_630] :
      ( r1_tarski(A_628,C_629)
      | ~ r1_tarski(B_630,C_629)
      | ~ r1_tarski(A_628,B_630) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4765,plain,(
    ! [A_628] :
      ( r1_tarski(A_628,u1_struct_0('#skF_5'))
      | ~ r1_tarski(A_628,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_4759,c_4760])).

tff(c_4748,plain,(
    ~ r2_hidden('#skF_6','#skF_8') ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_64,plain,(
    ! [D_87] :
      ( ~ r2_hidden('#skF_6',D_87)
      | ~ r1_tarski(D_87,'#skF_7')
      | ~ v3_pre_topc(D_87,'#skF_5')
      | ~ m1_subset_1(D_87,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | r2_hidden('#skF_6','#skF_8') ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_4832,plain,(
    ! [D_639] :
      ( ~ r2_hidden('#skF_6',D_639)
      | ~ r1_tarski(D_639,'#skF_7')
      | ~ v3_pre_topc(D_639,'#skF_5')
      | ~ m1_subset_1(D_639,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_4748,c_64])).

tff(c_4858,plain,(
    ! [A_643] :
      ( ~ r2_hidden('#skF_6',A_643)
      | ~ r1_tarski(A_643,'#skF_7')
      | ~ v3_pre_topc(A_643,'#skF_5')
      | ~ r1_tarski(A_643,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_6,c_4832])).

tff(c_4870,plain,(
    ! [A_628] :
      ( ~ r2_hidden('#skF_6',A_628)
      | ~ v3_pre_topc(A_628,'#skF_5')
      | ~ r1_tarski(A_628,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_4765,c_4858])).

tff(c_4893,plain,(
    ! [A_648] :
      ( ~ r2_hidden('#skF_6',k1_tops_1('#skF_5',A_648))
      | ~ r1_tarski(k1_tops_1('#skF_5',A_648),'#skF_7')
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | ~ r1_tarski(A_648,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_4889,c_4870])).

tff(c_4896,plain,(
    ! [A_648] :
      ( ~ r2_hidden('#skF_6',k1_tops_1('#skF_5',A_648))
      | ~ r1_tarski(k1_tops_1('#skF_5',A_648),'#skF_7')
      | ~ r1_tarski(A_648,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_4893])).

tff(c_5676,plain,
    ( ~ r1_tarski(k1_tops_1('#skF_5','#skF_7'),'#skF_7')
    | ~ r1_tarski('#skF_7',u1_struct_0('#skF_5'))
    | ~ m1_connsp_2('#skF_7','#skF_5','#skF_6')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_5669,c_4896])).

tff(c_5684,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_4747,c_4759,c_4816,c_5676])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:22:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.51/2.51  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.51/2.52  
% 7.51/2.52  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.51/2.53  %$ m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_8 > #skF_2 > #skF_4
% 7.51/2.53  
% 7.51/2.53  %Foreground sorts:
% 7.51/2.53  
% 7.51/2.53  
% 7.51/2.53  %Background operators:
% 7.51/2.53  
% 7.51/2.53  
% 7.51/2.53  %Foreground operators:
% 7.51/2.53  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 7.51/2.53  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 7.51/2.53  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 7.51/2.53  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 7.51/2.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.51/2.53  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.51/2.53  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 7.51/2.53  tff('#skF_7', type, '#skF_7': $i).
% 7.51/2.53  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 7.51/2.53  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.51/2.53  tff('#skF_5', type, '#skF_5': $i).
% 7.51/2.53  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 7.51/2.53  tff('#skF_6', type, '#skF_6': $i).
% 7.51/2.53  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.51/2.53  tff('#skF_8', type, '#skF_8': $i).
% 7.51/2.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.51/2.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.51/2.53  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 7.51/2.53  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 7.51/2.53  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 7.51/2.53  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 7.51/2.53  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.51/2.53  
% 7.51/2.56  tff(f_141, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m1_connsp_2(C, A, B) <=> (?[D]: (((m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) & v3_pre_topc(D, A)) & r1_tarski(D, C)) & r2_hidden(B, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_connsp_2)).
% 7.51/2.56  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 7.51/2.56  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 7.51/2.56  tff(f_43, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_tops_1)).
% 7.51/2.56  tff(f_64, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & r1_tarski(B, C)) => r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_tops_1)).
% 7.51/2.56  tff(f_50, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tops_1)).
% 7.51/2.56  tff(f_85, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (((m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) & v3_pre_topc(D, A)) & r1_tarski(D, B)) & r2_hidden(C, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t57_tops_1)).
% 7.51/2.56  tff(f_102, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m1_connsp_2(C, A, B) <=> r2_hidden(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_connsp_2)).
% 7.51/2.56  tff(c_52, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_141])).
% 7.51/2.56  tff(c_70, plain, (m1_connsp_2('#skF_7', '#skF_5', '#skF_6') | r1_tarski('#skF_8', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_141])).
% 7.51/2.56  tff(c_90, plain, (r1_tarski('#skF_8', '#skF_7')), inference(splitLeft, [status(thm)], [c_70])).
% 7.51/2.56  tff(c_50, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_141])).
% 7.51/2.56  tff(c_81, plain, (![A_90, B_91]: (r1_tarski(A_90, B_91) | ~m1_subset_1(A_90, k1_zfmisc_1(B_91)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.51/2.56  tff(c_89, plain, (r1_tarski('#skF_7', u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_50, c_81])).
% 7.51/2.56  tff(c_2380, plain, (![A_259, C_260, B_261]: (r1_tarski(A_259, C_260) | ~r1_tarski(B_261, C_260) | ~r1_tarski(A_259, B_261))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.51/2.56  tff(c_2391, plain, (![A_263]: (r1_tarski(A_263, u1_struct_0('#skF_5')) | ~r1_tarski(A_263, '#skF_7'))), inference(resolution, [status(thm)], [c_89, c_2380])).
% 7.51/2.56  tff(c_6, plain, (![A_4, B_5]: (m1_subset_1(A_4, k1_zfmisc_1(B_5)) | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.51/2.56  tff(c_74, plain, (m1_connsp_2('#skF_7', '#skF_5', '#skF_6') | v3_pre_topc('#skF_8', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_141])).
% 7.51/2.56  tff(c_91, plain, (v3_pre_topc('#skF_8', '#skF_5')), inference(splitLeft, [status(thm)], [c_74])).
% 7.51/2.56  tff(c_66, plain, (m1_connsp_2('#skF_7', '#skF_5', '#skF_6') | r2_hidden('#skF_6', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_141])).
% 7.51/2.56  tff(c_80, plain, (r2_hidden('#skF_6', '#skF_8')), inference(splitLeft, [status(thm)], [c_66])).
% 7.51/2.56  tff(c_78, plain, (m1_connsp_2('#skF_7', '#skF_5', '#skF_6') | m1_subset_1('#skF_8', k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_141])).
% 7.51/2.56  tff(c_92, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(splitLeft, [status(thm)], [c_78])).
% 7.51/2.56  tff(c_58, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_141])).
% 7.51/2.56  tff(c_60, plain, (![D_87]: (~r2_hidden('#skF_6', D_87) | ~r1_tarski(D_87, '#skF_7') | ~v3_pre_topc(D_87, '#skF_5') | ~m1_subset_1(D_87, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_connsp_2('#skF_7', '#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_141])).
% 7.51/2.56  tff(c_297, plain, (~m1_connsp_2('#skF_7', '#skF_5', '#skF_6')), inference(splitLeft, [status(thm)], [c_60])).
% 7.51/2.56  tff(c_56, plain, (v2_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_141])).
% 7.51/2.56  tff(c_54, plain, (l1_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_141])).
% 7.51/2.56  tff(c_214, plain, (![A_106, B_107]: (v3_pre_topc(k1_tops_1(A_106, B_107), A_106) | ~m1_subset_1(B_107, k1_zfmisc_1(u1_struct_0(A_106))) | ~l1_pre_topc(A_106) | ~v2_pre_topc(A_106))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.51/2.56  tff(c_221, plain, (v3_pre_topc(k1_tops_1('#skF_5', '#skF_7'), '#skF_5') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_50, c_214])).
% 7.51/2.56  tff(c_228, plain, (v3_pre_topc(k1_tops_1('#skF_5', '#skF_7'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_221])).
% 7.51/2.56  tff(c_765, plain, (![B_200, A_201, C_202]: (r1_tarski(B_200, k1_tops_1(A_201, C_202)) | ~r1_tarski(B_200, C_202) | ~v3_pre_topc(B_200, A_201) | ~m1_subset_1(C_202, k1_zfmisc_1(u1_struct_0(A_201))) | ~m1_subset_1(B_200, k1_zfmisc_1(u1_struct_0(A_201))) | ~l1_pre_topc(A_201))), inference(cnfTransformation, [status(thm)], [f_64])).
% 7.51/2.56  tff(c_774, plain, (![B_200]: (r1_tarski(B_200, k1_tops_1('#skF_5', '#skF_7')) | ~r1_tarski(B_200, '#skF_7') | ~v3_pre_topc(B_200, '#skF_5') | ~m1_subset_1(B_200, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5'))), inference(resolution, [status(thm)], [c_50, c_765])).
% 7.51/2.56  tff(c_783, plain, (![B_203]: (r1_tarski(B_203, k1_tops_1('#skF_5', '#skF_7')) | ~r1_tarski(B_203, '#skF_7') | ~v3_pre_topc(B_203, '#skF_5') | ~m1_subset_1(B_203, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_774])).
% 7.51/2.56  tff(c_790, plain, (r1_tarski('#skF_8', k1_tops_1('#skF_5', '#skF_7')) | ~r1_tarski('#skF_8', '#skF_7') | ~v3_pre_topc('#skF_8', '#skF_5')), inference(resolution, [status(thm)], [c_92, c_783])).
% 7.51/2.56  tff(c_803, plain, (r1_tarski('#skF_8', k1_tops_1('#skF_5', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_91, c_90, c_790])).
% 7.51/2.56  tff(c_142, plain, (![A_100, B_101]: (r1_tarski(k1_tops_1(A_100, B_101), B_101) | ~m1_subset_1(B_101, k1_zfmisc_1(u1_struct_0(A_100))) | ~l1_pre_topc(A_100))), inference(cnfTransformation, [status(thm)], [f_50])).
% 7.51/2.56  tff(c_149, plain, (r1_tarski(k1_tops_1('#skF_5', '#skF_7'), '#skF_7') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_50, c_142])).
% 7.51/2.56  tff(c_156, plain, (r1_tarski(k1_tops_1('#skF_5', '#skF_7'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_149])).
% 7.51/2.56  tff(c_97, plain, (![A_92, C_93, B_94]: (r1_tarski(A_92, C_93) | ~r1_tarski(B_94, C_93) | ~r1_tarski(A_92, B_94))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.51/2.56  tff(c_105, plain, (![A_92]: (r1_tarski(A_92, u1_struct_0('#skF_5')) | ~r1_tarski(A_92, '#skF_7'))), inference(resolution, [status(thm)], [c_89, c_97])).
% 7.51/2.56  tff(c_769, plain, (![B_200]: (r1_tarski(B_200, k1_tops_1('#skF_5', '#skF_8')) | ~r1_tarski(B_200, '#skF_8') | ~v3_pre_topc(B_200, '#skF_5') | ~m1_subset_1(B_200, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5'))), inference(resolution, [status(thm)], [c_92, c_765])).
% 7.51/2.56  tff(c_1013, plain, (![B_208]: (r1_tarski(B_208, k1_tops_1('#skF_5', '#skF_8')) | ~r1_tarski(B_208, '#skF_8') | ~v3_pre_topc(B_208, '#skF_5') | ~m1_subset_1(B_208, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_769])).
% 7.51/2.56  tff(c_1036, plain, (![A_209]: (r1_tarski(A_209, k1_tops_1('#skF_5', '#skF_8')) | ~r1_tarski(A_209, '#skF_8') | ~v3_pre_topc(A_209, '#skF_5') | ~r1_tarski(A_209, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_6, c_1013])).
% 7.51/2.56  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(B_2, C_3) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.51/2.56  tff(c_1759, plain, (![A_237, A_238]: (r1_tarski(A_237, k1_tops_1('#skF_5', '#skF_8')) | ~r1_tarski(A_237, A_238) | ~r1_tarski(A_238, '#skF_8') | ~v3_pre_topc(A_238, '#skF_5') | ~r1_tarski(A_238, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_1036, c_2])).
% 7.51/2.56  tff(c_1783, plain, (r1_tarski('#skF_8', k1_tops_1('#skF_5', '#skF_8')) | ~r1_tarski(k1_tops_1('#skF_5', '#skF_7'), '#skF_8') | ~v3_pre_topc(k1_tops_1('#skF_5', '#skF_7'), '#skF_5') | ~r1_tarski(k1_tops_1('#skF_5', '#skF_7'), u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_803, c_1759])).
% 7.51/2.56  tff(c_1869, plain, (r1_tarski('#skF_8', k1_tops_1('#skF_5', '#skF_8')) | ~r1_tarski(k1_tops_1('#skF_5', '#skF_7'), '#skF_8') | ~r1_tarski(k1_tops_1('#skF_5', '#skF_7'), u1_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_228, c_1783])).
% 7.51/2.56  tff(c_1966, plain, (~r1_tarski(k1_tops_1('#skF_5', '#skF_7'), u1_struct_0('#skF_5'))), inference(splitLeft, [status(thm)], [c_1869])).
% 7.51/2.56  tff(c_1978, plain, (~r1_tarski(k1_tops_1('#skF_5', '#skF_7'), '#skF_7')), inference(resolution, [status(thm)], [c_105, c_1966])).
% 7.51/2.56  tff(c_1989, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_156, c_1978])).
% 7.51/2.56  tff(c_1991, plain, (r1_tarski(k1_tops_1('#skF_5', '#skF_7'), u1_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_1869])).
% 7.51/2.56  tff(c_2098, plain, (![C_244, B_245, D_246, A_247]: (r2_hidden(C_244, B_245) | ~r2_hidden(C_244, D_246) | ~r1_tarski(D_246, B_245) | ~v3_pre_topc(D_246, A_247) | ~m1_subset_1(D_246, k1_zfmisc_1(u1_struct_0(A_247))) | ~v3_pre_topc(B_245, A_247) | ~m1_subset_1(B_245, k1_zfmisc_1(u1_struct_0(A_247))) | ~l1_pre_topc(A_247) | ~v2_pre_topc(A_247))), inference(cnfTransformation, [status(thm)], [f_85])).
% 7.51/2.56  tff(c_2220, plain, (![B_252, A_253]: (r2_hidden('#skF_6', B_252) | ~r1_tarski('#skF_8', B_252) | ~v3_pre_topc('#skF_8', A_253) | ~m1_subset_1('#skF_8', k1_zfmisc_1(u1_struct_0(A_253))) | ~v3_pre_topc(B_252, A_253) | ~m1_subset_1(B_252, k1_zfmisc_1(u1_struct_0(A_253))) | ~l1_pre_topc(A_253) | ~v2_pre_topc(A_253))), inference(resolution, [status(thm)], [c_80, c_2098])).
% 7.51/2.56  tff(c_2222, plain, (![B_252]: (r2_hidden('#skF_6', B_252) | ~r1_tarski('#skF_8', B_252) | ~v3_pre_topc('#skF_8', '#skF_5') | ~v3_pre_topc(B_252, '#skF_5') | ~m1_subset_1(B_252, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5'))), inference(resolution, [status(thm)], [c_92, c_2220])).
% 7.51/2.56  tff(c_2230, plain, (![B_254]: (r2_hidden('#skF_6', B_254) | ~r1_tarski('#skF_8', B_254) | ~v3_pre_topc(B_254, '#skF_5') | ~m1_subset_1(B_254, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_91, c_2222])).
% 7.51/2.56  tff(c_2262, plain, (![A_255]: (r2_hidden('#skF_6', A_255) | ~r1_tarski('#skF_8', A_255) | ~v3_pre_topc(A_255, '#skF_5') | ~r1_tarski(A_255, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_6, c_2230])).
% 7.51/2.56  tff(c_2268, plain, (r2_hidden('#skF_6', k1_tops_1('#skF_5', '#skF_7')) | ~r1_tarski('#skF_8', k1_tops_1('#skF_5', '#skF_7')) | ~v3_pre_topc(k1_tops_1('#skF_5', '#skF_7'), '#skF_5')), inference(resolution, [status(thm)], [c_1991, c_2262])).
% 7.51/2.56  tff(c_2321, plain, (r2_hidden('#skF_6', k1_tops_1('#skF_5', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_228, c_803, c_2268])).
% 7.51/2.56  tff(c_44, plain, (![C_64, A_58, B_62]: (m1_connsp_2(C_64, A_58, B_62) | ~r2_hidden(B_62, k1_tops_1(A_58, C_64)) | ~m1_subset_1(C_64, k1_zfmisc_1(u1_struct_0(A_58))) | ~m1_subset_1(B_62, u1_struct_0(A_58)) | ~l1_pre_topc(A_58) | ~v2_pre_topc(A_58) | v2_struct_0(A_58))), inference(cnfTransformation, [status(thm)], [f_102])).
% 7.51/2.56  tff(c_2348, plain, (m1_connsp_2('#skF_7', '#skF_5', '#skF_6') | ~m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_2321, c_44])).
% 7.51/2.56  tff(c_2352, plain, (m1_connsp_2('#skF_7', '#skF_5', '#skF_6') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_50, c_2348])).
% 7.51/2.56  tff(c_2354, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_297, c_2352])).
% 7.51/2.56  tff(c_2358, plain, (![D_258]: (~r2_hidden('#skF_6', D_258) | ~r1_tarski(D_258, '#skF_7') | ~v3_pre_topc(D_258, '#skF_5') | ~m1_subset_1(D_258, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(splitRight, [status(thm)], [c_60])).
% 7.51/2.56  tff(c_2361, plain, (~r2_hidden('#skF_6', '#skF_8') | ~r1_tarski('#skF_8', '#skF_7') | ~v3_pre_topc('#skF_8', '#skF_5')), inference(resolution, [status(thm)], [c_92, c_2358])).
% 7.51/2.56  tff(c_2372, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_91, c_90, c_80, c_2361])).
% 7.51/2.56  tff(c_2374, plain, (~m1_subset_1('#skF_8', k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(splitRight, [status(thm)], [c_78])).
% 7.51/2.56  tff(c_2378, plain, (~r1_tarski('#skF_8', u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_6, c_2374])).
% 7.51/2.56  tff(c_2396, plain, (~r1_tarski('#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_2391, c_2378])).
% 7.51/2.56  tff(c_2401, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_90, c_2396])).
% 7.51/2.56  tff(c_2402, plain, (m1_connsp_2('#skF_7', '#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_74])).
% 7.51/2.56  tff(c_2447, plain, (![A_272, B_273]: (r1_tarski(k1_tops_1(A_272, B_273), B_273) | ~m1_subset_1(B_273, k1_zfmisc_1(u1_struct_0(A_272))) | ~l1_pre_topc(A_272))), inference(cnfTransformation, [status(thm)], [f_50])).
% 7.51/2.56  tff(c_2452, plain, (r1_tarski(k1_tops_1('#skF_5', '#skF_7'), '#skF_7') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_50, c_2447])).
% 7.51/2.56  tff(c_2456, plain, (r1_tarski(k1_tops_1('#skF_5', '#skF_7'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_2452])).
% 7.51/2.56  tff(c_3297, plain, (![B_389, A_390, C_391]: (r2_hidden(B_389, k1_tops_1(A_390, C_391)) | ~m1_connsp_2(C_391, A_390, B_389) | ~m1_subset_1(C_391, k1_zfmisc_1(u1_struct_0(A_390))) | ~m1_subset_1(B_389, u1_struct_0(A_390)) | ~l1_pre_topc(A_390) | ~v2_pre_topc(A_390) | v2_struct_0(A_390))), inference(cnfTransformation, [status(thm)], [f_102])).
% 7.51/2.56  tff(c_3306, plain, (![B_389]: (r2_hidden(B_389, k1_tops_1('#skF_5', '#skF_7')) | ~m1_connsp_2('#skF_7', '#skF_5', B_389) | ~m1_subset_1(B_389, u1_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_50, c_3297])).
% 7.51/2.56  tff(c_3312, plain, (![B_389]: (r2_hidden(B_389, k1_tops_1('#skF_5', '#skF_7')) | ~m1_connsp_2('#skF_7', '#skF_5', B_389) | ~m1_subset_1(B_389, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_3306])).
% 7.51/2.56  tff(c_3314, plain, (![B_392]: (r2_hidden(B_392, k1_tops_1('#skF_5', '#skF_7')) | ~m1_connsp_2('#skF_7', '#skF_5', B_392) | ~m1_subset_1(B_392, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_58, c_3312])).
% 7.51/2.56  tff(c_2488, plain, (![A_277, B_278]: (v3_pre_topc(k1_tops_1(A_277, B_278), A_277) | ~m1_subset_1(B_278, k1_zfmisc_1(u1_struct_0(A_277))) | ~l1_pre_topc(A_277) | ~v2_pre_topc(A_277))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.51/2.56  tff(c_2494, plain, (![A_277, A_4]: (v3_pre_topc(k1_tops_1(A_277, A_4), A_277) | ~l1_pre_topc(A_277) | ~v2_pre_topc(A_277) | ~r1_tarski(A_4, u1_struct_0(A_277)))), inference(resolution, [status(thm)], [c_6, c_2488])).
% 7.51/2.56  tff(c_2405, plain, (![A_264, C_265, B_266]: (r1_tarski(A_264, C_265) | ~r1_tarski(B_266, C_265) | ~r1_tarski(A_264, B_266))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.51/2.56  tff(c_2410, plain, (![A_264]: (r1_tarski(A_264, u1_struct_0('#skF_5')) | ~r1_tarski(A_264, '#skF_7'))), inference(resolution, [status(thm)], [c_89, c_2405])).
% 7.51/2.56  tff(c_2403, plain, (~v3_pre_topc('#skF_8', '#skF_5')), inference(splitRight, [status(thm)], [c_74])).
% 7.51/2.56  tff(c_72, plain, (![D_87]: (~r2_hidden('#skF_6', D_87) | ~r1_tarski(D_87, '#skF_7') | ~v3_pre_topc(D_87, '#skF_5') | ~m1_subset_1(D_87, k1_zfmisc_1(u1_struct_0('#skF_5'))) | v3_pre_topc('#skF_8', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_141])).
% 7.51/2.56  tff(c_2421, plain, (![D_269]: (~r2_hidden('#skF_6', D_269) | ~r1_tarski(D_269, '#skF_7') | ~v3_pre_topc(D_269, '#skF_5') | ~m1_subset_1(D_269, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_2403, c_72])).
% 7.51/2.56  tff(c_2515, plain, (![A_283]: (~r2_hidden('#skF_6', A_283) | ~r1_tarski(A_283, '#skF_7') | ~v3_pre_topc(A_283, '#skF_5') | ~r1_tarski(A_283, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_6, c_2421])).
% 7.51/2.56  tff(c_2529, plain, (![A_284]: (~r2_hidden('#skF_6', A_284) | ~v3_pre_topc(A_284, '#skF_5') | ~r1_tarski(A_284, '#skF_7'))), inference(resolution, [status(thm)], [c_2410, c_2515])).
% 7.51/2.56  tff(c_2533, plain, (![A_4]: (~r2_hidden('#skF_6', k1_tops_1('#skF_5', A_4)) | ~r1_tarski(k1_tops_1('#skF_5', A_4), '#skF_7') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | ~r1_tarski(A_4, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_2494, c_2529])).
% 7.51/2.56  tff(c_2539, plain, (![A_4]: (~r2_hidden('#skF_6', k1_tops_1('#skF_5', A_4)) | ~r1_tarski(k1_tops_1('#skF_5', A_4), '#skF_7') | ~r1_tarski(A_4, u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_2533])).
% 7.51/2.56  tff(c_3321, plain, (~r1_tarski(k1_tops_1('#skF_5', '#skF_7'), '#skF_7') | ~r1_tarski('#skF_7', u1_struct_0('#skF_5')) | ~m1_connsp_2('#skF_7', '#skF_5', '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_3314, c_2539])).
% 7.51/2.56  tff(c_3329, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_2402, c_89, c_2456, c_3321])).
% 7.51/2.56  tff(c_3330, plain, (m1_connsp_2('#skF_7', '#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_70])).
% 7.51/2.56  tff(c_3350, plain, (![A_399, B_400]: (r1_tarski(k1_tops_1(A_399, B_400), B_400) | ~m1_subset_1(B_400, k1_zfmisc_1(u1_struct_0(A_399))) | ~l1_pre_topc(A_399))), inference(cnfTransformation, [status(thm)], [f_50])).
% 7.51/2.56  tff(c_3355, plain, (r1_tarski(k1_tops_1('#skF_5', '#skF_7'), '#skF_7') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_50, c_3350])).
% 7.51/2.56  tff(c_3359, plain, (r1_tarski(k1_tops_1('#skF_5', '#skF_7'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_3355])).
% 7.51/2.56  tff(c_4708, plain, (![B_622, A_623, C_624]: (r2_hidden(B_622, k1_tops_1(A_623, C_624)) | ~m1_connsp_2(C_624, A_623, B_622) | ~m1_subset_1(C_624, k1_zfmisc_1(u1_struct_0(A_623))) | ~m1_subset_1(B_622, u1_struct_0(A_623)) | ~l1_pre_topc(A_623) | ~v2_pre_topc(A_623) | v2_struct_0(A_623))), inference(cnfTransformation, [status(thm)], [f_102])).
% 7.51/2.56  tff(c_4717, plain, (![B_622]: (r2_hidden(B_622, k1_tops_1('#skF_5', '#skF_7')) | ~m1_connsp_2('#skF_7', '#skF_5', B_622) | ~m1_subset_1(B_622, u1_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_50, c_4708])).
% 7.51/2.56  tff(c_4723, plain, (![B_622]: (r2_hidden(B_622, k1_tops_1('#skF_5', '#skF_7')) | ~m1_connsp_2('#skF_7', '#skF_5', B_622) | ~m1_subset_1(B_622, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_4717])).
% 7.51/2.56  tff(c_4725, plain, (![B_625]: (r2_hidden(B_625, k1_tops_1('#skF_5', '#skF_7')) | ~m1_connsp_2('#skF_7', '#skF_5', B_625) | ~m1_subset_1(B_625, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_58, c_4723])).
% 7.51/2.56  tff(c_4030, plain, (![A_512, B_513]: (v3_pre_topc(k1_tops_1(A_512, B_513), A_512) | ~m1_subset_1(B_513, k1_zfmisc_1(u1_struct_0(A_512))) | ~l1_pre_topc(A_512) | ~v2_pre_topc(A_512))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.51/2.56  tff(c_4036, plain, (![A_512, A_4]: (v3_pre_topc(k1_tops_1(A_512, A_4), A_512) | ~l1_pre_topc(A_512) | ~v2_pre_topc(A_512) | ~r1_tarski(A_4, u1_struct_0(A_512)))), inference(resolution, [status(thm)], [c_6, c_4030])).
% 7.51/2.56  tff(c_3334, plain, (![A_393, C_394, B_395]: (r1_tarski(A_393, C_394) | ~r1_tarski(B_395, C_394) | ~r1_tarski(A_393, B_395))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.51/2.56  tff(c_3337, plain, (![A_393]: (r1_tarski(A_393, u1_struct_0('#skF_5')) | ~r1_tarski(A_393, '#skF_7'))), inference(resolution, [status(thm)], [c_89, c_3334])).
% 7.51/2.56  tff(c_3331, plain, (~r1_tarski('#skF_8', '#skF_7')), inference(splitRight, [status(thm)], [c_70])).
% 7.51/2.56  tff(c_68, plain, (![D_87]: (~r2_hidden('#skF_6', D_87) | ~r1_tarski(D_87, '#skF_7') | ~v3_pre_topc(D_87, '#skF_5') | ~m1_subset_1(D_87, k1_zfmisc_1(u1_struct_0('#skF_5'))) | r1_tarski('#skF_8', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_141])).
% 7.51/2.56  tff(c_4041, plain, (![D_514]: (~r2_hidden('#skF_6', D_514) | ~r1_tarski(D_514, '#skF_7') | ~v3_pre_topc(D_514, '#skF_5') | ~m1_subset_1(D_514, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_3331, c_68])).
% 7.51/2.56  tff(c_4052, plain, (![A_517]: (~r2_hidden('#skF_6', A_517) | ~r1_tarski(A_517, '#skF_7') | ~v3_pre_topc(A_517, '#skF_5') | ~r1_tarski(A_517, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_6, c_4041])).
% 7.51/2.56  tff(c_4068, plain, (![A_518]: (~r2_hidden('#skF_6', A_518) | ~v3_pre_topc(A_518, '#skF_5') | ~r1_tarski(A_518, '#skF_7'))), inference(resolution, [status(thm)], [c_3337, c_4052])).
% 7.51/2.56  tff(c_4072, plain, (![A_4]: (~r2_hidden('#skF_6', k1_tops_1('#skF_5', A_4)) | ~r1_tarski(k1_tops_1('#skF_5', A_4), '#skF_7') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | ~r1_tarski(A_4, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_4036, c_4068])).
% 7.51/2.56  tff(c_4081, plain, (![A_4]: (~r2_hidden('#skF_6', k1_tops_1('#skF_5', A_4)) | ~r1_tarski(k1_tops_1('#skF_5', A_4), '#skF_7') | ~r1_tarski(A_4, u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_4072])).
% 7.51/2.56  tff(c_4734, plain, (~r1_tarski(k1_tops_1('#skF_5', '#skF_7'), '#skF_7') | ~r1_tarski('#skF_7', u1_struct_0('#skF_5')) | ~m1_connsp_2('#skF_7', '#skF_5', '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_4725, c_4081])).
% 7.51/2.56  tff(c_4746, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_3330, c_89, c_3359, c_4734])).
% 7.51/2.56  tff(c_4747, plain, (m1_connsp_2('#skF_7', '#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_66])).
% 7.51/2.56  tff(c_4751, plain, (![A_626, B_627]: (r1_tarski(A_626, B_627) | ~m1_subset_1(A_626, k1_zfmisc_1(B_627)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.51/2.56  tff(c_4759, plain, (r1_tarski('#skF_7', u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_50, c_4751])).
% 7.51/2.56  tff(c_4807, plain, (![A_637, B_638]: (r1_tarski(k1_tops_1(A_637, B_638), B_638) | ~m1_subset_1(B_638, k1_zfmisc_1(u1_struct_0(A_637))) | ~l1_pre_topc(A_637))), inference(cnfTransformation, [status(thm)], [f_50])).
% 7.51/2.56  tff(c_4812, plain, (r1_tarski(k1_tops_1('#skF_5', '#skF_7'), '#skF_7') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_50, c_4807])).
% 7.51/2.56  tff(c_4816, plain, (r1_tarski(k1_tops_1('#skF_5', '#skF_7'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_4812])).
% 7.51/2.56  tff(c_5652, plain, (![B_751, A_752, C_753]: (r2_hidden(B_751, k1_tops_1(A_752, C_753)) | ~m1_connsp_2(C_753, A_752, B_751) | ~m1_subset_1(C_753, k1_zfmisc_1(u1_struct_0(A_752))) | ~m1_subset_1(B_751, u1_struct_0(A_752)) | ~l1_pre_topc(A_752) | ~v2_pre_topc(A_752) | v2_struct_0(A_752))), inference(cnfTransformation, [status(thm)], [f_102])).
% 7.51/2.56  tff(c_5661, plain, (![B_751]: (r2_hidden(B_751, k1_tops_1('#skF_5', '#skF_7')) | ~m1_connsp_2('#skF_7', '#skF_5', B_751) | ~m1_subset_1(B_751, u1_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_50, c_5652])).
% 7.51/2.56  tff(c_5667, plain, (![B_751]: (r2_hidden(B_751, k1_tops_1('#skF_5', '#skF_7')) | ~m1_connsp_2('#skF_7', '#skF_5', B_751) | ~m1_subset_1(B_751, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_5661])).
% 7.51/2.56  tff(c_5669, plain, (![B_754]: (r2_hidden(B_754, k1_tops_1('#skF_5', '#skF_7')) | ~m1_connsp_2('#skF_7', '#skF_5', B_754) | ~m1_subset_1(B_754, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_58, c_5667])).
% 7.51/2.56  tff(c_4873, plain, (![A_645, B_646]: (v3_pre_topc(k1_tops_1(A_645, B_646), A_645) | ~m1_subset_1(B_646, k1_zfmisc_1(u1_struct_0(A_645))) | ~l1_pre_topc(A_645) | ~v2_pre_topc(A_645))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.51/2.56  tff(c_4889, plain, (![A_647, A_648]: (v3_pre_topc(k1_tops_1(A_647, A_648), A_647) | ~l1_pre_topc(A_647) | ~v2_pre_topc(A_647) | ~r1_tarski(A_648, u1_struct_0(A_647)))), inference(resolution, [status(thm)], [c_6, c_4873])).
% 7.51/2.56  tff(c_4760, plain, (![A_628, C_629, B_630]: (r1_tarski(A_628, C_629) | ~r1_tarski(B_630, C_629) | ~r1_tarski(A_628, B_630))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.51/2.56  tff(c_4765, plain, (![A_628]: (r1_tarski(A_628, u1_struct_0('#skF_5')) | ~r1_tarski(A_628, '#skF_7'))), inference(resolution, [status(thm)], [c_4759, c_4760])).
% 7.51/2.56  tff(c_4748, plain, (~r2_hidden('#skF_6', '#skF_8')), inference(splitRight, [status(thm)], [c_66])).
% 7.51/2.56  tff(c_64, plain, (![D_87]: (~r2_hidden('#skF_6', D_87) | ~r1_tarski(D_87, '#skF_7') | ~v3_pre_topc(D_87, '#skF_5') | ~m1_subset_1(D_87, k1_zfmisc_1(u1_struct_0('#skF_5'))) | r2_hidden('#skF_6', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_141])).
% 7.51/2.56  tff(c_4832, plain, (![D_639]: (~r2_hidden('#skF_6', D_639) | ~r1_tarski(D_639, '#skF_7') | ~v3_pre_topc(D_639, '#skF_5') | ~m1_subset_1(D_639, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_4748, c_64])).
% 7.51/2.56  tff(c_4858, plain, (![A_643]: (~r2_hidden('#skF_6', A_643) | ~r1_tarski(A_643, '#skF_7') | ~v3_pre_topc(A_643, '#skF_5') | ~r1_tarski(A_643, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_6, c_4832])).
% 7.51/2.56  tff(c_4870, plain, (![A_628]: (~r2_hidden('#skF_6', A_628) | ~v3_pre_topc(A_628, '#skF_5') | ~r1_tarski(A_628, '#skF_7'))), inference(resolution, [status(thm)], [c_4765, c_4858])).
% 7.51/2.56  tff(c_4893, plain, (![A_648]: (~r2_hidden('#skF_6', k1_tops_1('#skF_5', A_648)) | ~r1_tarski(k1_tops_1('#skF_5', A_648), '#skF_7') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | ~r1_tarski(A_648, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_4889, c_4870])).
% 7.51/2.56  tff(c_4896, plain, (![A_648]: (~r2_hidden('#skF_6', k1_tops_1('#skF_5', A_648)) | ~r1_tarski(k1_tops_1('#skF_5', A_648), '#skF_7') | ~r1_tarski(A_648, u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_4893])).
% 7.51/2.56  tff(c_5676, plain, (~r1_tarski(k1_tops_1('#skF_5', '#skF_7'), '#skF_7') | ~r1_tarski('#skF_7', u1_struct_0('#skF_5')) | ~m1_connsp_2('#skF_7', '#skF_5', '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_5669, c_4896])).
% 7.51/2.56  tff(c_5684, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_4747, c_4759, c_4816, c_5676])).
% 7.51/2.56  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.51/2.56  
% 7.51/2.56  Inference rules
% 7.51/2.56  ----------------------
% 7.51/2.56  #Ref     : 0
% 7.51/2.56  #Sup     : 1304
% 7.51/2.56  #Fact    : 0
% 7.51/2.56  #Define  : 0
% 7.51/2.56  #Split   : 36
% 7.51/2.56  #Chain   : 0
% 7.51/2.56  #Close   : 0
% 7.51/2.56  
% 7.51/2.56  Ordering : KBO
% 7.51/2.56  
% 7.51/2.56  Simplification rules
% 7.51/2.56  ----------------------
% 7.51/2.56  #Subsume      : 510
% 7.51/2.56  #Demod        : 685
% 7.51/2.56  #Tautology    : 88
% 7.51/2.56  #SimpNegUnit  : 31
% 7.51/2.56  #BackRed      : 0
% 7.51/2.56  
% 7.51/2.56  #Partial instantiations: 0
% 7.51/2.56  #Strategies tried      : 1
% 7.51/2.56  
% 7.51/2.56  Timing (in seconds)
% 7.51/2.56  ----------------------
% 7.51/2.56  Preprocessing        : 0.34
% 7.51/2.56  Parsing              : 0.18
% 7.51/2.56  CNF conversion       : 0.03
% 7.51/2.56  Main loop            : 1.43
% 7.51/2.56  Inferencing          : 0.46
% 7.51/2.56  Reduction            : 0.40
% 7.51/2.56  Demodulation         : 0.26
% 7.51/2.56  BG Simplification    : 0.05
% 7.51/2.56  Subsumption          : 0.43
% 7.51/2.56  Abstraction          : 0.06
% 7.51/2.56  MUC search           : 0.00
% 7.51/2.56  Cooper               : 0.00
% 7.51/2.56  Total                : 1.83
% 7.51/2.56  Index Insertion      : 0.00
% 7.51/2.56  Index Deletion       : 0.00
% 7.51/2.56  Index Matching       : 0.00
% 7.51/2.56  BG Taut test         : 0.00
%------------------------------------------------------------------------------
