%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:41 EST 2020

% Result     : Theorem 4.57s
% Output     : CNFRefutation 4.57s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 229 expanded)
%              Number of leaves         :   33 (  94 expanded)
%              Depth                    :   13
%              Number of atoms          :  152 ( 542 expanded)
%              Number of equality atoms :   45 ( 133 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v1_tops_1 > r2_hidden > m1_subset_1 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k9_subset_1 > k4_xboole_0 > k3_xboole_0 > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_tops_1,type,(
    v1_tops_1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

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

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_99,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v1_tops_1(B,A)
             => ! [C] :
                  ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
                 => ( v3_pre_topc(C,A)
                   => k2_pre_topc(A,C) = k2_pre_topc(A,k9_subset_1(u1_struct_0(A),C,B)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_tops_1)).

tff(f_59,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_55,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_38,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_40,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_68,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> k2_pre_topc(A,B) = k2_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tops_1)).

tff(f_82,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( v3_pre_topc(B,A)
               => k2_pre_topc(A,k9_subset_1(u1_struct_0(A),B,k2_pre_topc(A,C))) = k2_pre_topc(A,k9_subset_1(u1_struct_0(A),B,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_tops_1)).

tff(c_50,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_32,plain,(
    ! [A_19] :
      ( l1_struct_0(A_19)
      | ~ l1_pre_topc(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_65,plain,(
    ! [A_37] :
      ( u1_struct_0(A_37) = k2_struct_0(A_37)
      | ~ l1_struct_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_70,plain,(
    ! [A_38] :
      ( u1_struct_0(A_38) = k2_struct_0(A_38)
      | ~ l1_pre_topc(A_38) ) ),
    inference(resolution,[status(thm)],[c_32,c_65])).

tff(c_74,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_70])).

tff(c_48,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_77,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_48])).

tff(c_125,plain,(
    ! [A_55,B_56,C_57] :
      ( k9_subset_1(A_55,B_56,C_57) = k3_xboole_0(B_56,C_57)
      | ~ m1_subset_1(C_57,k1_zfmisc_1(A_55)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_132,plain,(
    ! [B_56] : k9_subset_1(k2_struct_0('#skF_3'),B_56,'#skF_4') = k3_xboole_0(B_56,'#skF_4') ),
    inference(resolution,[status(thm)],[c_77,c_125])).

tff(c_40,plain,(
    k2_pre_topc('#skF_3',k9_subset_1(u1_struct_0('#skF_3'),'#skF_5','#skF_4')) != k2_pre_topc('#skF_3','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_75,plain,(
    k2_pre_topc('#skF_3',k9_subset_1(k2_struct_0('#skF_3'),'#skF_5','#skF_4')) != k2_pre_topc('#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_40])).

tff(c_155,plain,(
    k2_pre_topc('#skF_3',k3_xboole_0('#skF_5','#skF_4')) != k2_pre_topc('#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_75])).

tff(c_44,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_76,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_44])).

tff(c_22,plain,(
    ! [A_9] : k2_subset_1(A_9) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_24,plain,(
    ! [A_10] : m1_subset_1(k2_subset_1(A_10),k1_zfmisc_1(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_53,plain,(
    ! [A_10] : m1_subset_1(A_10,k1_zfmisc_1(A_10)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_24])).

tff(c_306,plain,(
    ! [A_78,B_79,C_80] :
      ( r2_hidden('#skF_1'(A_78,B_79,C_80),A_78)
      | r2_hidden('#skF_2'(A_78,B_79,C_80),C_80)
      | k3_xboole_0(A_78,B_79) = C_80 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_26,plain,(
    ! [C_14,A_11,B_12] :
      ( r2_hidden(C_14,A_11)
      | ~ r2_hidden(C_14,B_12)
      | ~ m1_subset_1(B_12,k1_zfmisc_1(A_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_778,plain,(
    ! [A_132,B_133,C_134,A_135] :
      ( r2_hidden('#skF_1'(A_132,B_133,C_134),A_135)
      | ~ m1_subset_1(A_132,k1_zfmisc_1(A_135))
      | r2_hidden('#skF_2'(A_132,B_133,C_134),C_134)
      | k3_xboole_0(A_132,B_133) = C_134 ) ),
    inference(resolution,[status(thm)],[c_306,c_26])).

tff(c_14,plain,(
    ! [A_1,B_2,C_3] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2,C_3),C_3)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),C_3)
      | k3_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_832,plain,(
    ! [A_136,A_137,B_138] :
      ( ~ m1_subset_1(A_136,k1_zfmisc_1(A_137))
      | r2_hidden('#skF_2'(A_136,B_138,A_137),A_137)
      | k3_xboole_0(A_136,B_138) = A_137 ) ),
    inference(resolution,[status(thm)],[c_778,c_14])).

tff(c_858,plain,(
    ! [A_136,B_138,A_137,A_11] :
      ( r2_hidden('#skF_2'(A_136,B_138,A_137),A_11)
      | ~ m1_subset_1(A_137,k1_zfmisc_1(A_11))
      | ~ m1_subset_1(A_136,k1_zfmisc_1(A_137))
      | k3_xboole_0(A_136,B_138) = A_137 ) ),
    inference(resolution,[status(thm)],[c_832,c_26])).

tff(c_1410,plain,(
    ! [A_206,B_207,C_208,A_209] :
      ( r2_hidden('#skF_2'(A_206,B_207,C_208),A_209)
      | ~ m1_subset_1(C_208,k1_zfmisc_1(A_209))
      | r2_hidden('#skF_1'(A_206,B_207,C_208),A_206)
      | k3_xboole_0(A_206,B_207) = C_208 ) ),
    inference(resolution,[status(thm)],[c_306,c_26])).

tff(c_12,plain,(
    ! [A_1,B_2,C_3] :
      ( r2_hidden('#skF_1'(A_1,B_2,C_3),A_1)
      | ~ r2_hidden('#skF_2'(A_1,B_2,C_3),B_2)
      | ~ r2_hidden('#skF_2'(A_1,B_2,C_3),A_1)
      | k3_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1940,plain,(
    ! [A_246,A_247,C_248] :
      ( ~ r2_hidden('#skF_2'(A_246,A_247,C_248),A_246)
      | ~ m1_subset_1(C_248,k1_zfmisc_1(A_247))
      | r2_hidden('#skF_1'(A_246,A_247,C_248),A_246)
      | k3_xboole_0(A_246,A_247) = C_248 ) ),
    inference(resolution,[status(thm)],[c_1410,c_12])).

tff(c_8,plain,(
    ! [A_1,B_2,C_3] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2,C_3),C_3)
      | ~ r2_hidden('#skF_2'(A_1,B_2,C_3),B_2)
      | ~ r2_hidden('#skF_2'(A_1,B_2,C_3),A_1)
      | k3_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_2122,plain,(
    ! [A_257,A_258] :
      ( ~ r2_hidden('#skF_2'(A_257,A_258,A_257),A_258)
      | ~ r2_hidden('#skF_2'(A_257,A_258,A_257),A_257)
      | ~ m1_subset_1(A_257,k1_zfmisc_1(A_258))
      | k3_xboole_0(A_257,A_258) = A_257 ) ),
    inference(resolution,[status(thm)],[c_1940,c_8])).

tff(c_2143,plain,(
    ! [A_137,A_11] :
      ( ~ r2_hidden('#skF_2'(A_137,A_11,A_137),A_137)
      | ~ m1_subset_1(A_137,k1_zfmisc_1(A_11))
      | ~ m1_subset_1(A_137,k1_zfmisc_1(A_137))
      | k3_xboole_0(A_137,A_11) = A_137 ) ),
    inference(resolution,[status(thm)],[c_858,c_2122])).

tff(c_2225,plain,(
    ! [A_259,A_260] :
      ( ~ r2_hidden('#skF_2'(A_259,A_260,A_259),A_259)
      | ~ m1_subset_1(A_259,k1_zfmisc_1(A_260))
      | k3_xboole_0(A_259,A_260) = A_259 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_2143])).

tff(c_2243,plain,(
    ! [A_11,B_138] :
      ( ~ m1_subset_1(A_11,k1_zfmisc_1(B_138))
      | ~ m1_subset_1(A_11,k1_zfmisc_1(A_11))
      | k3_xboole_0(A_11,B_138) = A_11 ) ),
    inference(resolution,[status(thm)],[c_858,c_2225])).

tff(c_2417,plain,(
    ! [A_265,B_266] :
      ( ~ m1_subset_1(A_265,k1_zfmisc_1(B_266))
      | k3_xboole_0(A_265,B_266) = A_265 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_2243])).

tff(c_2428,plain,(
    k3_xboole_0('#skF_5',k2_struct_0('#skF_3')) = '#skF_5' ),
    inference(resolution,[status(thm)],[c_76,c_2417])).

tff(c_42,plain,(
    v3_pre_topc('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_134,plain,(
    ! [A_10,B_56] : k9_subset_1(A_10,B_56,A_10) = k3_xboole_0(B_56,A_10) ),
    inference(resolution,[status(thm)],[c_53,c_125])).

tff(c_46,plain,(
    v1_tops_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_144,plain,(
    ! [A_60,B_61] :
      ( k2_pre_topc(A_60,B_61) = k2_struct_0(A_60)
      | ~ v1_tops_1(B_61,A_60)
      | ~ m1_subset_1(B_61,k1_zfmisc_1(u1_struct_0(A_60)))
      | ~ l1_pre_topc(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_147,plain,(
    ! [B_61] :
      ( k2_pre_topc('#skF_3',B_61) = k2_struct_0('#skF_3')
      | ~ v1_tops_1(B_61,'#skF_3')
      | ~ m1_subset_1(B_61,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_144])).

tff(c_174,plain,(
    ! [B_64] :
      ( k2_pre_topc('#skF_3',B_64) = k2_struct_0('#skF_3')
      | ~ v1_tops_1(B_64,'#skF_3')
      | ~ m1_subset_1(B_64,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_147])).

tff(c_177,plain,
    ( k2_pre_topc('#skF_3','#skF_4') = k2_struct_0('#skF_3')
    | ~ v1_tops_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_77,c_174])).

tff(c_187,plain,(
    k2_pre_topc('#skF_3','#skF_4') = k2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_177])).

tff(c_52,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_610,plain,(
    ! [A_112,B_113,C_114] :
      ( k2_pre_topc(A_112,k9_subset_1(u1_struct_0(A_112),B_113,k2_pre_topc(A_112,C_114))) = k2_pre_topc(A_112,k9_subset_1(u1_struct_0(A_112),B_113,C_114))
      | ~ v3_pre_topc(B_113,A_112)
      | ~ m1_subset_1(C_114,k1_zfmisc_1(u1_struct_0(A_112)))
      | ~ m1_subset_1(B_113,k1_zfmisc_1(u1_struct_0(A_112)))
      | ~ l1_pre_topc(A_112)
      | ~ v2_pre_topc(A_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_628,plain,(
    ! [B_113,C_114] :
      ( k2_pre_topc('#skF_3',k9_subset_1(k2_struct_0('#skF_3'),B_113,k2_pre_topc('#skF_3',C_114))) = k2_pre_topc('#skF_3',k9_subset_1(u1_struct_0('#skF_3'),B_113,C_114))
      | ~ v3_pre_topc(B_113,'#skF_3')
      | ~ m1_subset_1(C_114,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(B_113,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_610])).

tff(c_719,plain,(
    ! [B_118,C_119] :
      ( k2_pre_topc('#skF_3',k9_subset_1(k2_struct_0('#skF_3'),B_118,k2_pre_topc('#skF_3',C_119))) = k2_pre_topc('#skF_3',k9_subset_1(k2_struct_0('#skF_3'),B_118,C_119))
      | ~ v3_pre_topc(B_118,'#skF_3')
      | ~ m1_subset_1(C_119,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ m1_subset_1(B_118,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_74,c_74,c_74,c_628])).

tff(c_741,plain,(
    ! [B_118] :
      ( k2_pre_topc('#skF_3',k9_subset_1(k2_struct_0('#skF_3'),B_118,k2_struct_0('#skF_3'))) = k2_pre_topc('#skF_3',k9_subset_1(k2_struct_0('#skF_3'),B_118,'#skF_4'))
      | ~ v3_pre_topc(B_118,'#skF_3')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ m1_subset_1(B_118,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_187,c_719])).

tff(c_1592,plain,(
    ! [B_227] :
      ( k2_pre_topc('#skF_3',k3_xboole_0(B_227,k2_struct_0('#skF_3'))) = k2_pre_topc('#skF_3',k3_xboole_0(B_227,'#skF_4'))
      | ~ v3_pre_topc(B_227,'#skF_3')
      | ~ m1_subset_1(B_227,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_132,c_134,c_741])).

tff(c_1598,plain,
    ( k2_pre_topc('#skF_3',k3_xboole_0('#skF_5',k2_struct_0('#skF_3'))) = k2_pre_topc('#skF_3',k3_xboole_0('#skF_5','#skF_4'))
    | ~ v3_pre_topc('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_1592])).

tff(c_1607,plain,(
    k2_pre_topc('#skF_3',k3_xboole_0('#skF_5',k2_struct_0('#skF_3'))) = k2_pre_topc('#skF_3',k3_xboole_0('#skF_5','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_1598])).

tff(c_2526,plain,(
    k2_pre_topc('#skF_3',k3_xboole_0('#skF_5','#skF_4')) = k2_pre_topc('#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2428,c_1607])).

tff(c_2528,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_155,c_2526])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:31:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.57/1.87  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.57/1.87  
% 4.57/1.87  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.57/1.87  %$ v3_pre_topc > v1_tops_1 > r2_hidden > m1_subset_1 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k9_subset_1 > k4_xboole_0 > k3_xboole_0 > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4
% 4.57/1.87  
% 4.57/1.87  %Foreground sorts:
% 4.57/1.87  
% 4.57/1.87  
% 4.57/1.87  %Background operators:
% 4.57/1.87  
% 4.57/1.87  
% 4.57/1.87  %Foreground operators:
% 4.57/1.87  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.57/1.87  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 4.57/1.87  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.57/1.87  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.57/1.87  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.57/1.87  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.57/1.87  tff('#skF_5', type, '#skF_5': $i).
% 4.57/1.87  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 4.57/1.87  tff('#skF_3', type, '#skF_3': $i).
% 4.57/1.87  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.57/1.87  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.57/1.87  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 4.57/1.87  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.57/1.87  tff('#skF_4', type, '#skF_4': $i).
% 4.57/1.87  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.57/1.87  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.57/1.87  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.57/1.87  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.57/1.87  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 4.57/1.87  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 4.57/1.87  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 4.57/1.87  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 4.57/1.87  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.57/1.87  
% 4.57/1.89  tff(f_99, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(C, A) => (k2_pre_topc(A, C) = k2_pre_topc(A, k9_subset_1(u1_struct_0(A), C, B))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_tops_1)).
% 4.57/1.89  tff(f_59, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 4.57/1.89  tff(f_55, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 4.57/1.89  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 4.57/1.89  tff(f_38, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 4.57/1.89  tff(f_40, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 4.57/1.89  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 4.57/1.89  tff(f_47, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 4.57/1.89  tff(f_68, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = k2_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tops_1)).
% 4.57/1.89  tff(f_82, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) => (k2_pre_topc(A, k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, C))) = k2_pre_topc(A, k9_subset_1(u1_struct_0(A), B, C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_tops_1)).
% 4.57/1.89  tff(c_50, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.57/1.89  tff(c_32, plain, (![A_19]: (l1_struct_0(A_19) | ~l1_pre_topc(A_19))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.57/1.89  tff(c_65, plain, (![A_37]: (u1_struct_0(A_37)=k2_struct_0(A_37) | ~l1_struct_0(A_37))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.57/1.89  tff(c_70, plain, (![A_38]: (u1_struct_0(A_38)=k2_struct_0(A_38) | ~l1_pre_topc(A_38))), inference(resolution, [status(thm)], [c_32, c_65])).
% 4.57/1.89  tff(c_74, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_50, c_70])).
% 4.57/1.89  tff(c_48, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.57/1.89  tff(c_77, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_48])).
% 4.57/1.89  tff(c_125, plain, (![A_55, B_56, C_57]: (k9_subset_1(A_55, B_56, C_57)=k3_xboole_0(B_56, C_57) | ~m1_subset_1(C_57, k1_zfmisc_1(A_55)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.57/1.89  tff(c_132, plain, (![B_56]: (k9_subset_1(k2_struct_0('#skF_3'), B_56, '#skF_4')=k3_xboole_0(B_56, '#skF_4'))), inference(resolution, [status(thm)], [c_77, c_125])).
% 4.57/1.89  tff(c_40, plain, (k2_pre_topc('#skF_3', k9_subset_1(u1_struct_0('#skF_3'), '#skF_5', '#skF_4'))!=k2_pre_topc('#skF_3', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.57/1.89  tff(c_75, plain, (k2_pre_topc('#skF_3', k9_subset_1(k2_struct_0('#skF_3'), '#skF_5', '#skF_4'))!=k2_pre_topc('#skF_3', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_40])).
% 4.57/1.89  tff(c_155, plain, (k2_pre_topc('#skF_3', k3_xboole_0('#skF_5', '#skF_4'))!=k2_pre_topc('#skF_3', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_132, c_75])).
% 4.57/1.89  tff(c_44, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.57/1.89  tff(c_76, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_44])).
% 4.57/1.89  tff(c_22, plain, (![A_9]: (k2_subset_1(A_9)=A_9)), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.57/1.89  tff(c_24, plain, (![A_10]: (m1_subset_1(k2_subset_1(A_10), k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.57/1.89  tff(c_53, plain, (![A_10]: (m1_subset_1(A_10, k1_zfmisc_1(A_10)))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_24])).
% 4.57/1.89  tff(c_306, plain, (![A_78, B_79, C_80]: (r2_hidden('#skF_1'(A_78, B_79, C_80), A_78) | r2_hidden('#skF_2'(A_78, B_79, C_80), C_80) | k3_xboole_0(A_78, B_79)=C_80)), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.57/1.89  tff(c_26, plain, (![C_14, A_11, B_12]: (r2_hidden(C_14, A_11) | ~r2_hidden(C_14, B_12) | ~m1_subset_1(B_12, k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.57/1.89  tff(c_778, plain, (![A_132, B_133, C_134, A_135]: (r2_hidden('#skF_1'(A_132, B_133, C_134), A_135) | ~m1_subset_1(A_132, k1_zfmisc_1(A_135)) | r2_hidden('#skF_2'(A_132, B_133, C_134), C_134) | k3_xboole_0(A_132, B_133)=C_134)), inference(resolution, [status(thm)], [c_306, c_26])).
% 4.57/1.89  tff(c_14, plain, (![A_1, B_2, C_3]: (~r2_hidden('#skF_1'(A_1, B_2, C_3), C_3) | r2_hidden('#skF_2'(A_1, B_2, C_3), C_3) | k3_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.57/1.89  tff(c_832, plain, (![A_136, A_137, B_138]: (~m1_subset_1(A_136, k1_zfmisc_1(A_137)) | r2_hidden('#skF_2'(A_136, B_138, A_137), A_137) | k3_xboole_0(A_136, B_138)=A_137)), inference(resolution, [status(thm)], [c_778, c_14])).
% 4.57/1.89  tff(c_858, plain, (![A_136, B_138, A_137, A_11]: (r2_hidden('#skF_2'(A_136, B_138, A_137), A_11) | ~m1_subset_1(A_137, k1_zfmisc_1(A_11)) | ~m1_subset_1(A_136, k1_zfmisc_1(A_137)) | k3_xboole_0(A_136, B_138)=A_137)), inference(resolution, [status(thm)], [c_832, c_26])).
% 4.57/1.89  tff(c_1410, plain, (![A_206, B_207, C_208, A_209]: (r2_hidden('#skF_2'(A_206, B_207, C_208), A_209) | ~m1_subset_1(C_208, k1_zfmisc_1(A_209)) | r2_hidden('#skF_1'(A_206, B_207, C_208), A_206) | k3_xboole_0(A_206, B_207)=C_208)), inference(resolution, [status(thm)], [c_306, c_26])).
% 4.57/1.89  tff(c_12, plain, (![A_1, B_2, C_3]: (r2_hidden('#skF_1'(A_1, B_2, C_3), A_1) | ~r2_hidden('#skF_2'(A_1, B_2, C_3), B_2) | ~r2_hidden('#skF_2'(A_1, B_2, C_3), A_1) | k3_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.57/1.89  tff(c_1940, plain, (![A_246, A_247, C_248]: (~r2_hidden('#skF_2'(A_246, A_247, C_248), A_246) | ~m1_subset_1(C_248, k1_zfmisc_1(A_247)) | r2_hidden('#skF_1'(A_246, A_247, C_248), A_246) | k3_xboole_0(A_246, A_247)=C_248)), inference(resolution, [status(thm)], [c_1410, c_12])).
% 4.57/1.89  tff(c_8, plain, (![A_1, B_2, C_3]: (~r2_hidden('#skF_1'(A_1, B_2, C_3), C_3) | ~r2_hidden('#skF_2'(A_1, B_2, C_3), B_2) | ~r2_hidden('#skF_2'(A_1, B_2, C_3), A_1) | k3_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.57/1.89  tff(c_2122, plain, (![A_257, A_258]: (~r2_hidden('#skF_2'(A_257, A_258, A_257), A_258) | ~r2_hidden('#skF_2'(A_257, A_258, A_257), A_257) | ~m1_subset_1(A_257, k1_zfmisc_1(A_258)) | k3_xboole_0(A_257, A_258)=A_257)), inference(resolution, [status(thm)], [c_1940, c_8])).
% 4.57/1.89  tff(c_2143, plain, (![A_137, A_11]: (~r2_hidden('#skF_2'(A_137, A_11, A_137), A_137) | ~m1_subset_1(A_137, k1_zfmisc_1(A_11)) | ~m1_subset_1(A_137, k1_zfmisc_1(A_137)) | k3_xboole_0(A_137, A_11)=A_137)), inference(resolution, [status(thm)], [c_858, c_2122])).
% 4.57/1.89  tff(c_2225, plain, (![A_259, A_260]: (~r2_hidden('#skF_2'(A_259, A_260, A_259), A_259) | ~m1_subset_1(A_259, k1_zfmisc_1(A_260)) | k3_xboole_0(A_259, A_260)=A_259)), inference(demodulation, [status(thm), theory('equality')], [c_53, c_2143])).
% 4.57/1.89  tff(c_2243, plain, (![A_11, B_138]: (~m1_subset_1(A_11, k1_zfmisc_1(B_138)) | ~m1_subset_1(A_11, k1_zfmisc_1(A_11)) | k3_xboole_0(A_11, B_138)=A_11)), inference(resolution, [status(thm)], [c_858, c_2225])).
% 4.57/1.89  tff(c_2417, plain, (![A_265, B_266]: (~m1_subset_1(A_265, k1_zfmisc_1(B_266)) | k3_xboole_0(A_265, B_266)=A_265)), inference(demodulation, [status(thm), theory('equality')], [c_53, c_2243])).
% 4.57/1.89  tff(c_2428, plain, (k3_xboole_0('#skF_5', k2_struct_0('#skF_3'))='#skF_5'), inference(resolution, [status(thm)], [c_76, c_2417])).
% 4.57/1.89  tff(c_42, plain, (v3_pre_topc('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.57/1.89  tff(c_134, plain, (![A_10, B_56]: (k9_subset_1(A_10, B_56, A_10)=k3_xboole_0(B_56, A_10))), inference(resolution, [status(thm)], [c_53, c_125])).
% 4.57/1.89  tff(c_46, plain, (v1_tops_1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.57/1.89  tff(c_144, plain, (![A_60, B_61]: (k2_pre_topc(A_60, B_61)=k2_struct_0(A_60) | ~v1_tops_1(B_61, A_60) | ~m1_subset_1(B_61, k1_zfmisc_1(u1_struct_0(A_60))) | ~l1_pre_topc(A_60))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.57/1.89  tff(c_147, plain, (![B_61]: (k2_pre_topc('#skF_3', B_61)=k2_struct_0('#skF_3') | ~v1_tops_1(B_61, '#skF_3') | ~m1_subset_1(B_61, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_74, c_144])).
% 4.57/1.89  tff(c_174, plain, (![B_64]: (k2_pre_topc('#skF_3', B_64)=k2_struct_0('#skF_3') | ~v1_tops_1(B_64, '#skF_3') | ~m1_subset_1(B_64, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_147])).
% 4.57/1.89  tff(c_177, plain, (k2_pre_topc('#skF_3', '#skF_4')=k2_struct_0('#skF_3') | ~v1_tops_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_77, c_174])).
% 4.57/1.89  tff(c_187, plain, (k2_pre_topc('#skF_3', '#skF_4')=k2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_177])).
% 4.57/1.89  tff(c_52, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.57/1.89  tff(c_610, plain, (![A_112, B_113, C_114]: (k2_pre_topc(A_112, k9_subset_1(u1_struct_0(A_112), B_113, k2_pre_topc(A_112, C_114)))=k2_pre_topc(A_112, k9_subset_1(u1_struct_0(A_112), B_113, C_114)) | ~v3_pre_topc(B_113, A_112) | ~m1_subset_1(C_114, k1_zfmisc_1(u1_struct_0(A_112))) | ~m1_subset_1(B_113, k1_zfmisc_1(u1_struct_0(A_112))) | ~l1_pre_topc(A_112) | ~v2_pre_topc(A_112))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.57/1.89  tff(c_628, plain, (![B_113, C_114]: (k2_pre_topc('#skF_3', k9_subset_1(k2_struct_0('#skF_3'), B_113, k2_pre_topc('#skF_3', C_114)))=k2_pre_topc('#skF_3', k9_subset_1(u1_struct_0('#skF_3'), B_113, C_114)) | ~v3_pre_topc(B_113, '#skF_3') | ~m1_subset_1(C_114, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1(B_113, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_74, c_610])).
% 4.57/1.89  tff(c_719, plain, (![B_118, C_119]: (k2_pre_topc('#skF_3', k9_subset_1(k2_struct_0('#skF_3'), B_118, k2_pre_topc('#skF_3', C_119)))=k2_pre_topc('#skF_3', k9_subset_1(k2_struct_0('#skF_3'), B_118, C_119)) | ~v3_pre_topc(B_118, '#skF_3') | ~m1_subset_1(C_119, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_subset_1(B_118, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_74, c_74, c_74, c_628])).
% 4.57/1.89  tff(c_741, plain, (![B_118]: (k2_pre_topc('#skF_3', k9_subset_1(k2_struct_0('#skF_3'), B_118, k2_struct_0('#skF_3')))=k2_pre_topc('#skF_3', k9_subset_1(k2_struct_0('#skF_3'), B_118, '#skF_4')) | ~v3_pre_topc(B_118, '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_subset_1(B_118, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(superposition, [status(thm), theory('equality')], [c_187, c_719])).
% 4.57/1.89  tff(c_1592, plain, (![B_227]: (k2_pre_topc('#skF_3', k3_xboole_0(B_227, k2_struct_0('#skF_3')))=k2_pre_topc('#skF_3', k3_xboole_0(B_227, '#skF_4')) | ~v3_pre_topc(B_227, '#skF_3') | ~m1_subset_1(B_227, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_77, c_132, c_134, c_741])).
% 4.57/1.89  tff(c_1598, plain, (k2_pre_topc('#skF_3', k3_xboole_0('#skF_5', k2_struct_0('#skF_3')))=k2_pre_topc('#skF_3', k3_xboole_0('#skF_5', '#skF_4')) | ~v3_pre_topc('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_76, c_1592])).
% 4.57/1.89  tff(c_1607, plain, (k2_pre_topc('#skF_3', k3_xboole_0('#skF_5', k2_struct_0('#skF_3')))=k2_pre_topc('#skF_3', k3_xboole_0('#skF_5', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_1598])).
% 4.57/1.89  tff(c_2526, plain, (k2_pre_topc('#skF_3', k3_xboole_0('#skF_5', '#skF_4'))=k2_pre_topc('#skF_3', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2428, c_1607])).
% 4.57/1.89  tff(c_2528, plain, $false, inference(negUnitSimplification, [status(thm)], [c_155, c_2526])).
% 4.57/1.89  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.57/1.89  
% 4.57/1.89  Inference rules
% 4.57/1.89  ----------------------
% 4.57/1.89  #Ref     : 0
% 4.57/1.89  #Sup     : 547
% 4.57/1.89  #Fact    : 0
% 4.57/1.89  #Define  : 0
% 4.57/1.89  #Split   : 4
% 4.57/1.89  #Chain   : 0
% 4.57/1.89  #Close   : 0
% 4.57/1.89  
% 4.57/1.89  Ordering : KBO
% 4.57/1.89  
% 4.57/1.89  Simplification rules
% 4.57/1.89  ----------------------
% 4.57/1.89  #Subsume      : 117
% 4.57/1.89  #Demod        : 310
% 4.57/1.89  #Tautology    : 113
% 4.57/1.89  #SimpNegUnit  : 4
% 4.57/1.89  #BackRed      : 5
% 4.57/1.89  
% 4.57/1.89  #Partial instantiations: 0
% 4.57/1.89  #Strategies tried      : 1
% 4.57/1.89  
% 4.57/1.89  Timing (in seconds)
% 4.57/1.89  ----------------------
% 4.57/1.89  Preprocessing        : 0.33
% 4.57/1.89  Parsing              : 0.17
% 4.57/1.89  CNF conversion       : 0.02
% 4.57/1.89  Main loop            : 0.79
% 4.57/1.89  Inferencing          : 0.27
% 4.57/1.89  Reduction            : 0.24
% 4.57/1.89  Demodulation         : 0.16
% 4.57/1.89  BG Simplification    : 0.04
% 4.57/1.89  Subsumption          : 0.19
% 4.57/1.89  Abstraction          : 0.05
% 4.57/1.90  MUC search           : 0.00
% 4.57/1.90  Cooper               : 0.00
% 4.57/1.90  Total                : 1.16
% 4.57/1.90  Index Insertion      : 0.00
% 4.57/1.90  Index Deletion       : 0.00
% 4.57/1.90  Index Matching       : 0.00
% 4.57/1.90  BG Taut test         : 0.00
%------------------------------------------------------------------------------
