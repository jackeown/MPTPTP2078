%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:40 EST 2020

% Result     : Theorem 7.01s
% Output     : CNFRefutation 7.09s
% Verified   : 
% Statistics : Number of formulae       :  115 (2994 expanded)
%              Number of leaves         :   34 (1022 expanded)
%              Depth                    :   21
%              Number of atoms          :  216 (8322 expanded)
%              Number of equality atoms :   66 (1947 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v1_tops_1 > r2_hidden > m1_subset_1 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4

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

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_tops_1)).

tff(f_59,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_55,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_36,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_38,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_68,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> k2_pre_topc(A,B) = k2_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tops_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_tops_1)).

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

tff(c_94,plain,(
    ! [A_50,B_51,C_52] :
      ( k9_subset_1(A_50,B_51,C_52) = k3_xboole_0(B_51,C_52)
      | ~ m1_subset_1(C_52,k1_zfmisc_1(A_50)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_101,plain,(
    ! [B_51] : k9_subset_1(k2_struct_0('#skF_3'),B_51,'#skF_4') = k3_xboole_0(B_51,'#skF_4') ),
    inference(resolution,[status(thm)],[c_77,c_94])).

tff(c_40,plain,(
    k2_pre_topc('#skF_3',k9_subset_1(u1_struct_0('#skF_3'),'#skF_5','#skF_4')) != k2_pre_topc('#skF_3','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_75,plain,(
    k2_pre_topc('#skF_3',k9_subset_1(k2_struct_0('#skF_3'),'#skF_5','#skF_4')) != k2_pre_topc('#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_40])).

tff(c_113,plain,(
    k2_pre_topc('#skF_3',k3_xboole_0('#skF_5','#skF_4')) != k2_pre_topc('#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_75])).

tff(c_44,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_76,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_44])).

tff(c_20,plain,(
    ! [A_7] : k2_subset_1(A_7) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_22,plain,(
    ! [A_8] : m1_subset_1(k2_subset_1(A_8),k1_zfmisc_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_53,plain,(
    ! [A_8] : m1_subset_1(A_8,k1_zfmisc_1(A_8)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_22])).

tff(c_294,plain,(
    ! [A_83,B_84,C_85] :
      ( r2_hidden('#skF_1'(A_83,B_84,C_85),B_84)
      | r2_hidden('#skF_2'(A_83,B_84,C_85),C_85)
      | k3_xboole_0(A_83,B_84) = C_85 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_24,plain,(
    ! [C_12,A_9,B_10] :
      ( r2_hidden(C_12,A_9)
      | ~ r2_hidden(C_12,B_10)
      | ~ m1_subset_1(B_10,k1_zfmisc_1(A_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_914,plain,(
    ! [A_173,B_174,C_175,A_176] :
      ( r2_hidden('#skF_1'(A_173,B_174,C_175),A_176)
      | ~ m1_subset_1(B_174,k1_zfmisc_1(A_176))
      | r2_hidden('#skF_2'(A_173,B_174,C_175),C_175)
      | k3_xboole_0(A_173,B_174) = C_175 ) ),
    inference(resolution,[status(thm)],[c_294,c_24])).

tff(c_14,plain,(
    ! [A_1,B_2,C_3] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2,C_3),C_3)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),C_3)
      | k3_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_958,plain,(
    ! [B_177,A_178,A_179] :
      ( ~ m1_subset_1(B_177,k1_zfmisc_1(A_178))
      | r2_hidden('#skF_2'(A_179,B_177,A_178),A_178)
      | k3_xboole_0(A_179,B_177) = A_178 ) ),
    inference(resolution,[status(thm)],[c_914,c_14])).

tff(c_979,plain,(
    ! [A_179,B_177,A_178,A_9] :
      ( r2_hidden('#skF_2'(A_179,B_177,A_178),A_9)
      | ~ m1_subset_1(A_178,k1_zfmisc_1(A_9))
      | ~ m1_subset_1(B_177,k1_zfmisc_1(A_178))
      | k3_xboole_0(A_179,B_177) = A_178 ) ),
    inference(resolution,[status(thm)],[c_958,c_24])).

tff(c_831,plain,(
    ! [A_162,B_163,C_164,A_165] :
      ( r2_hidden('#skF_2'(A_162,B_163,C_164),A_165)
      | ~ m1_subset_1(C_164,k1_zfmisc_1(A_165))
      | r2_hidden('#skF_1'(A_162,B_163,C_164),B_163)
      | k3_xboole_0(A_162,B_163) = C_164 ) ),
    inference(resolution,[status(thm)],[c_294,c_24])).

tff(c_10,plain,(
    ! [A_1,B_2,C_3] :
      ( r2_hidden('#skF_1'(A_1,B_2,C_3),B_2)
      | ~ r2_hidden('#skF_2'(A_1,B_2,C_3),B_2)
      | ~ r2_hidden('#skF_2'(A_1,B_2,C_3),A_1)
      | k3_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1120,plain,(
    ! [A_199,B_200,C_201] :
      ( ~ r2_hidden('#skF_2'(A_199,B_200,C_201),B_200)
      | ~ m1_subset_1(C_201,k1_zfmisc_1(A_199))
      | r2_hidden('#skF_1'(A_199,B_200,C_201),B_200)
      | k3_xboole_0(A_199,B_200) = C_201 ) ),
    inference(resolution,[status(thm)],[c_831,c_10])).

tff(c_8,plain,(
    ! [A_1,B_2,C_3] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2,C_3),C_3)
      | ~ r2_hidden('#skF_2'(A_1,B_2,C_3),B_2)
      | ~ r2_hidden('#skF_2'(A_1,B_2,C_3),A_1)
      | k3_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1675,plain,(
    ! [A_244,B_245] :
      ( ~ r2_hidden('#skF_2'(A_244,B_245,B_245),A_244)
      | ~ r2_hidden('#skF_2'(A_244,B_245,B_245),B_245)
      | ~ m1_subset_1(B_245,k1_zfmisc_1(A_244))
      | k3_xboole_0(A_244,B_245) = B_245 ) ),
    inference(resolution,[status(thm)],[c_1120,c_8])).

tff(c_1700,plain,(
    ! [A_9,A_178] :
      ( ~ r2_hidden('#skF_2'(A_9,A_178,A_178),A_178)
      | ~ m1_subset_1(A_178,k1_zfmisc_1(A_9))
      | ~ m1_subset_1(A_178,k1_zfmisc_1(A_178))
      | k3_xboole_0(A_9,A_178) = A_178 ) ),
    inference(resolution,[status(thm)],[c_979,c_1675])).

tff(c_1794,plain,(
    ! [A_246,A_247] :
      ( ~ r2_hidden('#skF_2'(A_246,A_247,A_247),A_247)
      | ~ m1_subset_1(A_247,k1_zfmisc_1(A_246))
      | k3_xboole_0(A_246,A_247) = A_247 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_1700])).

tff(c_1822,plain,(
    ! [A_9,A_179] :
      ( ~ m1_subset_1(A_9,k1_zfmisc_1(A_179))
      | ~ m1_subset_1(A_9,k1_zfmisc_1(A_9))
      | k3_xboole_0(A_179,A_9) = A_9 ) ),
    inference(resolution,[status(thm)],[c_979,c_1794])).

tff(c_1918,plain,(
    ! [A_248,A_249] :
      ( ~ m1_subset_1(A_248,k1_zfmisc_1(A_249))
      | k3_xboole_0(A_249,A_248) = A_248 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_1822])).

tff(c_1929,plain,(
    k3_xboole_0(k2_struct_0('#skF_3'),'#skF_5') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_76,c_1918])).

tff(c_234,plain,(
    ! [A_75,B_76,C_77] :
      ( r2_hidden('#skF_1'(A_75,B_76,C_77),A_75)
      | r2_hidden('#skF_2'(A_75,B_76,C_77),C_77)
      | k3_xboole_0(A_75,B_76) = C_77 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_266,plain,(
    ! [A_78,B_79] :
      ( r2_hidden('#skF_2'(A_78,B_79,A_78),A_78)
      | k3_xboole_0(A_78,B_79) = A_78 ) ),
    inference(resolution,[status(thm)],[c_234,c_14])).

tff(c_6,plain,(
    ! [D_6,A_1,B_2] :
      ( r2_hidden(D_6,A_1)
      | ~ r2_hidden(D_6,k3_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_278,plain,(
    ! [A_1,B_2,B_79] :
      ( r2_hidden('#skF_2'(k3_xboole_0(A_1,B_2),B_79,k3_xboole_0(A_1,B_2)),A_1)
      | k3_xboole_0(k3_xboole_0(A_1,B_2),B_79) = k3_xboole_0(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_266,c_6])).

tff(c_2056,plain,(
    ! [B_79] :
      ( r2_hidden('#skF_2'(k3_xboole_0(k2_struct_0('#skF_3'),'#skF_5'),B_79,'#skF_5'),k2_struct_0('#skF_3'))
      | k3_xboole_0(k3_xboole_0(k2_struct_0('#skF_3'),'#skF_5'),B_79) = k3_xboole_0(k2_struct_0('#skF_3'),'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1929,c_278])).

tff(c_2225,plain,(
    ! [B_256] :
      ( r2_hidden('#skF_2'('#skF_5',B_256,'#skF_5'),k2_struct_0('#skF_3'))
      | k3_xboole_0('#skF_5',B_256) = '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1929,c_1929,c_1929,c_2056])).

tff(c_16,plain,(
    ! [A_1,B_2,C_3] :
      ( r2_hidden('#skF_1'(A_1,B_2,C_3),B_2)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),C_3)
      | k3_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_415,plain,(
    ! [A_116,B_117,C_118] :
      ( r2_hidden('#skF_1'(A_116,B_117,C_118),B_117)
      | ~ r2_hidden('#skF_2'(A_116,B_117,C_118),B_117)
      | ~ r2_hidden('#skF_2'(A_116,B_117,C_118),A_116)
      | k3_xboole_0(A_116,B_117) = C_118 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_442,plain,(
    ! [C_119,B_120] :
      ( ~ r2_hidden('#skF_2'(C_119,B_120,C_119),B_120)
      | r2_hidden('#skF_1'(C_119,B_120,C_119),B_120)
      | k3_xboole_0(C_119,B_120) = C_119 ) ),
    inference(resolution,[status(thm)],[c_16,c_415])).

tff(c_462,plain,(
    ! [C_119,B_120,A_9] :
      ( r2_hidden('#skF_1'(C_119,B_120,C_119),A_9)
      | ~ m1_subset_1(B_120,k1_zfmisc_1(A_9))
      | ~ r2_hidden('#skF_2'(C_119,B_120,C_119),B_120)
      | k3_xboole_0(C_119,B_120) = C_119 ) ),
    inference(resolution,[status(thm)],[c_442,c_24])).

tff(c_2234,plain,(
    ! [A_9] :
      ( r2_hidden('#skF_1'('#skF_5',k2_struct_0('#skF_3'),'#skF_5'),A_9)
      | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(A_9))
      | k3_xboole_0('#skF_5',k2_struct_0('#skF_3')) = '#skF_5' ) ),
    inference(resolution,[status(thm)],[c_2225,c_462])).

tff(c_3264,plain,(
    k3_xboole_0('#skF_5',k2_struct_0('#skF_3')) = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_2234])).

tff(c_42,plain,(
    v3_pre_topc('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_52,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_103,plain,(
    ! [A_8,B_51] : k9_subset_1(A_8,B_51,A_8) = k3_xboole_0(B_51,A_8) ),
    inference(resolution,[status(thm)],[c_53,c_94])).

tff(c_46,plain,(
    v1_tops_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_178,plain,(
    ! [A_64,B_65] :
      ( k2_pre_topc(A_64,B_65) = k2_struct_0(A_64)
      | ~ v1_tops_1(B_65,A_64)
      | ~ m1_subset_1(B_65,k1_zfmisc_1(u1_struct_0(A_64)))
      | ~ l1_pre_topc(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_181,plain,(
    ! [B_65] :
      ( k2_pre_topc('#skF_3',B_65) = k2_struct_0('#skF_3')
      | ~ v1_tops_1(B_65,'#skF_3')
      | ~ m1_subset_1(B_65,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_178])).

tff(c_206,plain,(
    ! [B_70] :
      ( k2_pre_topc('#skF_3',B_70) = k2_struct_0('#skF_3')
      | ~ v1_tops_1(B_70,'#skF_3')
      | ~ m1_subset_1(B_70,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_181])).

tff(c_209,plain,
    ( k2_pre_topc('#skF_3','#skF_4') = k2_struct_0('#skF_3')
    | ~ v1_tops_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_77,c_206])).

tff(c_219,plain,(
    k2_pre_topc('#skF_3','#skF_4') = k2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_209])).

tff(c_609,plain,(
    ! [A_128,B_129,C_130] :
      ( k2_pre_topc(A_128,k9_subset_1(u1_struct_0(A_128),B_129,k2_pre_topc(A_128,C_130))) = k2_pre_topc(A_128,k9_subset_1(u1_struct_0(A_128),B_129,C_130))
      | ~ v3_pre_topc(B_129,A_128)
      | ~ m1_subset_1(C_130,k1_zfmisc_1(u1_struct_0(A_128)))
      | ~ m1_subset_1(B_129,k1_zfmisc_1(u1_struct_0(A_128)))
      | ~ l1_pre_topc(A_128)
      | ~ v2_pre_topc(A_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_624,plain,(
    ! [B_129] :
      ( k2_pre_topc('#skF_3',k9_subset_1(u1_struct_0('#skF_3'),B_129,k2_struct_0('#skF_3'))) = k2_pre_topc('#skF_3',k9_subset_1(u1_struct_0('#skF_3'),B_129,'#skF_4'))
      | ~ v3_pre_topc(B_129,'#skF_3')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(B_129,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_219,c_609])).

tff(c_877,plain,(
    ! [B_169] :
      ( k2_pre_topc('#skF_3',k3_xboole_0(B_169,k2_struct_0('#skF_3'))) = k2_pre_topc('#skF_3',k3_xboole_0(B_169,'#skF_4'))
      | ~ v3_pre_topc(B_169,'#skF_3')
      | ~ m1_subset_1(B_169,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_74,c_77,c_74,c_101,c_103,c_74,c_74,c_624])).

tff(c_883,plain,
    ( k2_pre_topc('#skF_3',k3_xboole_0('#skF_5',k2_struct_0('#skF_3'))) = k2_pre_topc('#skF_3',k3_xboole_0('#skF_5','#skF_4'))
    | ~ v3_pre_topc('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_877])).

tff(c_892,plain,(
    k2_pre_topc('#skF_3',k3_xboole_0('#skF_5',k2_struct_0('#skF_3'))) = k2_pre_topc('#skF_3',k3_xboole_0('#skF_5','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_883])).

tff(c_3265,plain,(
    k2_pre_topc('#skF_3',k3_xboole_0('#skF_5','#skF_4')) = k2_pre_topc('#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3264,c_892])).

tff(c_3267,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_113,c_3265])).

tff(c_3269,plain,(
    k3_xboole_0('#skF_5',k2_struct_0('#skF_3')) != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_2234])).

tff(c_2096,plain,(
    ! [B_79] :
      ( r2_hidden('#skF_2'('#skF_5',B_79,'#skF_5'),k2_struct_0('#skF_3'))
      | k3_xboole_0('#skF_5',B_79) = '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1929,c_1929,c_1929,c_2056])).

tff(c_1030,plain,(
    ! [A_188,B_189,C_190,A_191] :
      ( r2_hidden('#skF_1'(A_188,B_189,C_190),A_191)
      | ~ m1_subset_1(A_188,k1_zfmisc_1(A_191))
      | r2_hidden('#skF_2'(A_188,B_189,C_190),C_190)
      | k3_xboole_0(A_188,B_189) = C_190 ) ),
    inference(resolution,[status(thm)],[c_234,c_24])).

tff(c_1074,plain,(
    ! [A_192,A_193,B_194] :
      ( ~ m1_subset_1(A_192,k1_zfmisc_1(A_193))
      | r2_hidden('#skF_2'(A_192,B_194,A_193),A_193)
      | k3_xboole_0(A_192,B_194) = A_193 ) ),
    inference(resolution,[status(thm)],[c_1030,c_14])).

tff(c_1095,plain,(
    ! [A_192,B_194,A_193,A_9] :
      ( r2_hidden('#skF_2'(A_192,B_194,A_193),A_9)
      | ~ m1_subset_1(A_193,k1_zfmisc_1(A_9))
      | ~ m1_subset_1(A_192,k1_zfmisc_1(A_193))
      | k3_xboole_0(A_192,B_194) = A_193 ) ),
    inference(resolution,[status(thm)],[c_1074,c_24])).

tff(c_12,plain,(
    ! [A_1,B_2,C_3] :
      ( r2_hidden('#skF_1'(A_1,B_2,C_3),A_1)
      | ~ r2_hidden('#skF_2'(A_1,B_2,C_3),B_2)
      | ~ r2_hidden('#skF_2'(A_1,B_2,C_3),A_1)
      | k3_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_2235,plain,
    ( r2_hidden('#skF_1'('#skF_5',k2_struct_0('#skF_3'),'#skF_5'),'#skF_5')
    | ~ r2_hidden('#skF_2'('#skF_5',k2_struct_0('#skF_3'),'#skF_5'),'#skF_5')
    | k3_xboole_0('#skF_5',k2_struct_0('#skF_3')) = '#skF_5' ),
    inference(resolution,[status(thm)],[c_2225,c_12])).

tff(c_4591,plain,
    ( r2_hidden('#skF_1'('#skF_5',k2_struct_0('#skF_3'),'#skF_5'),'#skF_5')
    | ~ r2_hidden('#skF_2'('#skF_5',k2_struct_0('#skF_3'),'#skF_5'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_3269,c_2235])).

tff(c_4592,plain,(
    ~ r2_hidden('#skF_2'('#skF_5',k2_struct_0('#skF_3'),'#skF_5'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_4591])).

tff(c_4596,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_5'))
    | k3_xboole_0('#skF_5',k2_struct_0('#skF_3')) = '#skF_5' ),
    inference(resolution,[status(thm)],[c_1095,c_4592])).

tff(c_4620,plain,(
    k3_xboole_0('#skF_5',k2_struct_0('#skF_3')) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_4596])).

tff(c_4622,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3269,c_4620])).

tff(c_4624,plain,(
    r2_hidden('#skF_2'('#skF_5',k2_struct_0('#skF_3'),'#skF_5'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_4591])).

tff(c_4623,plain,(
    r2_hidden('#skF_1'('#skF_5',k2_struct_0('#skF_3'),'#skF_5'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_4591])).

tff(c_4844,plain,(
    ! [A_393] :
      ( r2_hidden('#skF_1'('#skF_5',k2_struct_0('#skF_3'),'#skF_5'),A_393)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_393)) ) ),
    inference(resolution,[status(thm)],[c_4623,c_24])).

tff(c_4847,plain,
    ( ~ r2_hidden('#skF_2'('#skF_5',k2_struct_0('#skF_3'),'#skF_5'),k2_struct_0('#skF_3'))
    | ~ r2_hidden('#skF_2'('#skF_5',k2_struct_0('#skF_3'),'#skF_5'),'#skF_5')
    | k3_xboole_0('#skF_5',k2_struct_0('#skF_3')) = '#skF_5'
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_4844,c_8])).

tff(c_4864,plain,
    ( ~ r2_hidden('#skF_2'('#skF_5',k2_struct_0('#skF_3'),'#skF_5'),k2_struct_0('#skF_3'))
    | k3_xboole_0('#skF_5',k2_struct_0('#skF_3')) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_4624,c_4847])).

tff(c_4865,plain,(
    ~ r2_hidden('#skF_2'('#skF_5',k2_struct_0('#skF_3'),'#skF_5'),k2_struct_0('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_3269,c_4864])).

tff(c_4882,plain,(
    k3_xboole_0('#skF_5',k2_struct_0('#skF_3')) = '#skF_5' ),
    inference(resolution,[status(thm)],[c_2096,c_4865])).

tff(c_4916,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3269,c_4882])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:31:46 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.01/2.41  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.09/2.42  
% 7.09/2.42  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.09/2.42  %$ v3_pre_topc > v1_tops_1 > r2_hidden > m1_subset_1 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4
% 7.09/2.42  
% 7.09/2.42  %Foreground sorts:
% 7.09/2.42  
% 7.09/2.42  
% 7.09/2.42  %Background operators:
% 7.09/2.42  
% 7.09/2.42  
% 7.09/2.42  %Foreground operators:
% 7.09/2.42  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 7.09/2.42  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 7.09/2.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.09/2.42  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.09/2.42  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 7.09/2.42  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.09/2.42  tff('#skF_5', type, '#skF_5': $i).
% 7.09/2.42  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 7.09/2.42  tff('#skF_3', type, '#skF_3': $i).
% 7.09/2.42  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 7.09/2.42  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.09/2.42  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 7.09/2.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.09/2.42  tff('#skF_4', type, '#skF_4': $i).
% 7.09/2.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.09/2.42  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 7.09/2.42  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.09/2.42  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 7.09/2.42  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 7.09/2.42  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 7.09/2.42  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 7.09/2.42  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 7.09/2.42  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.09/2.42  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 7.09/2.42  
% 7.09/2.45  tff(f_99, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(C, A) => (k2_pre_topc(A, C) = k2_pre_topc(A, k9_subset_1(u1_struct_0(A), C, B))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_tops_1)).
% 7.09/2.45  tff(f_59, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 7.09/2.45  tff(f_55, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 7.09/2.45  tff(f_49, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 7.09/2.45  tff(f_36, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 7.09/2.45  tff(f_38, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 7.09/2.45  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 7.09/2.45  tff(f_45, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 7.09/2.45  tff(f_68, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = k2_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tops_1)).
% 7.09/2.45  tff(f_82, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) => (k2_pre_topc(A, k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, C))) = k2_pre_topc(A, k9_subset_1(u1_struct_0(A), B, C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_tops_1)).
% 7.09/2.45  tff(c_50, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_99])).
% 7.09/2.45  tff(c_32, plain, (![A_19]: (l1_struct_0(A_19) | ~l1_pre_topc(A_19))), inference(cnfTransformation, [status(thm)], [f_59])).
% 7.09/2.45  tff(c_65, plain, (![A_37]: (u1_struct_0(A_37)=k2_struct_0(A_37) | ~l1_struct_0(A_37))), inference(cnfTransformation, [status(thm)], [f_55])).
% 7.09/2.45  tff(c_70, plain, (![A_38]: (u1_struct_0(A_38)=k2_struct_0(A_38) | ~l1_pre_topc(A_38))), inference(resolution, [status(thm)], [c_32, c_65])).
% 7.09/2.45  tff(c_74, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_50, c_70])).
% 7.09/2.45  tff(c_48, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_99])).
% 7.09/2.45  tff(c_77, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_48])).
% 7.09/2.45  tff(c_94, plain, (![A_50, B_51, C_52]: (k9_subset_1(A_50, B_51, C_52)=k3_xboole_0(B_51, C_52) | ~m1_subset_1(C_52, k1_zfmisc_1(A_50)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.09/2.45  tff(c_101, plain, (![B_51]: (k9_subset_1(k2_struct_0('#skF_3'), B_51, '#skF_4')=k3_xboole_0(B_51, '#skF_4'))), inference(resolution, [status(thm)], [c_77, c_94])).
% 7.09/2.45  tff(c_40, plain, (k2_pre_topc('#skF_3', k9_subset_1(u1_struct_0('#skF_3'), '#skF_5', '#skF_4'))!=k2_pre_topc('#skF_3', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_99])).
% 7.09/2.45  tff(c_75, plain, (k2_pre_topc('#skF_3', k9_subset_1(k2_struct_0('#skF_3'), '#skF_5', '#skF_4'))!=k2_pre_topc('#skF_3', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_40])).
% 7.09/2.45  tff(c_113, plain, (k2_pre_topc('#skF_3', k3_xboole_0('#skF_5', '#skF_4'))!=k2_pre_topc('#skF_3', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_101, c_75])).
% 7.09/2.45  tff(c_44, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_99])).
% 7.09/2.45  tff(c_76, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_44])).
% 7.09/2.45  tff(c_20, plain, (![A_7]: (k2_subset_1(A_7)=A_7)), inference(cnfTransformation, [status(thm)], [f_36])).
% 7.09/2.45  tff(c_22, plain, (![A_8]: (m1_subset_1(k2_subset_1(A_8), k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.09/2.45  tff(c_53, plain, (![A_8]: (m1_subset_1(A_8, k1_zfmisc_1(A_8)))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_22])).
% 7.09/2.45  tff(c_294, plain, (![A_83, B_84, C_85]: (r2_hidden('#skF_1'(A_83, B_84, C_85), B_84) | r2_hidden('#skF_2'(A_83, B_84, C_85), C_85) | k3_xboole_0(A_83, B_84)=C_85)), inference(cnfTransformation, [status(thm)], [f_34])).
% 7.09/2.45  tff(c_24, plain, (![C_12, A_9, B_10]: (r2_hidden(C_12, A_9) | ~r2_hidden(C_12, B_10) | ~m1_subset_1(B_10, k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.09/2.45  tff(c_914, plain, (![A_173, B_174, C_175, A_176]: (r2_hidden('#skF_1'(A_173, B_174, C_175), A_176) | ~m1_subset_1(B_174, k1_zfmisc_1(A_176)) | r2_hidden('#skF_2'(A_173, B_174, C_175), C_175) | k3_xboole_0(A_173, B_174)=C_175)), inference(resolution, [status(thm)], [c_294, c_24])).
% 7.09/2.45  tff(c_14, plain, (![A_1, B_2, C_3]: (~r2_hidden('#skF_1'(A_1, B_2, C_3), C_3) | r2_hidden('#skF_2'(A_1, B_2, C_3), C_3) | k3_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_34])).
% 7.09/2.45  tff(c_958, plain, (![B_177, A_178, A_179]: (~m1_subset_1(B_177, k1_zfmisc_1(A_178)) | r2_hidden('#skF_2'(A_179, B_177, A_178), A_178) | k3_xboole_0(A_179, B_177)=A_178)), inference(resolution, [status(thm)], [c_914, c_14])).
% 7.09/2.45  tff(c_979, plain, (![A_179, B_177, A_178, A_9]: (r2_hidden('#skF_2'(A_179, B_177, A_178), A_9) | ~m1_subset_1(A_178, k1_zfmisc_1(A_9)) | ~m1_subset_1(B_177, k1_zfmisc_1(A_178)) | k3_xboole_0(A_179, B_177)=A_178)), inference(resolution, [status(thm)], [c_958, c_24])).
% 7.09/2.45  tff(c_831, plain, (![A_162, B_163, C_164, A_165]: (r2_hidden('#skF_2'(A_162, B_163, C_164), A_165) | ~m1_subset_1(C_164, k1_zfmisc_1(A_165)) | r2_hidden('#skF_1'(A_162, B_163, C_164), B_163) | k3_xboole_0(A_162, B_163)=C_164)), inference(resolution, [status(thm)], [c_294, c_24])).
% 7.09/2.45  tff(c_10, plain, (![A_1, B_2, C_3]: (r2_hidden('#skF_1'(A_1, B_2, C_3), B_2) | ~r2_hidden('#skF_2'(A_1, B_2, C_3), B_2) | ~r2_hidden('#skF_2'(A_1, B_2, C_3), A_1) | k3_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_34])).
% 7.09/2.45  tff(c_1120, plain, (![A_199, B_200, C_201]: (~r2_hidden('#skF_2'(A_199, B_200, C_201), B_200) | ~m1_subset_1(C_201, k1_zfmisc_1(A_199)) | r2_hidden('#skF_1'(A_199, B_200, C_201), B_200) | k3_xboole_0(A_199, B_200)=C_201)), inference(resolution, [status(thm)], [c_831, c_10])).
% 7.09/2.45  tff(c_8, plain, (![A_1, B_2, C_3]: (~r2_hidden('#skF_1'(A_1, B_2, C_3), C_3) | ~r2_hidden('#skF_2'(A_1, B_2, C_3), B_2) | ~r2_hidden('#skF_2'(A_1, B_2, C_3), A_1) | k3_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_34])).
% 7.09/2.45  tff(c_1675, plain, (![A_244, B_245]: (~r2_hidden('#skF_2'(A_244, B_245, B_245), A_244) | ~r2_hidden('#skF_2'(A_244, B_245, B_245), B_245) | ~m1_subset_1(B_245, k1_zfmisc_1(A_244)) | k3_xboole_0(A_244, B_245)=B_245)), inference(resolution, [status(thm)], [c_1120, c_8])).
% 7.09/2.45  tff(c_1700, plain, (![A_9, A_178]: (~r2_hidden('#skF_2'(A_9, A_178, A_178), A_178) | ~m1_subset_1(A_178, k1_zfmisc_1(A_9)) | ~m1_subset_1(A_178, k1_zfmisc_1(A_178)) | k3_xboole_0(A_9, A_178)=A_178)), inference(resolution, [status(thm)], [c_979, c_1675])).
% 7.09/2.45  tff(c_1794, plain, (![A_246, A_247]: (~r2_hidden('#skF_2'(A_246, A_247, A_247), A_247) | ~m1_subset_1(A_247, k1_zfmisc_1(A_246)) | k3_xboole_0(A_246, A_247)=A_247)), inference(demodulation, [status(thm), theory('equality')], [c_53, c_1700])).
% 7.09/2.45  tff(c_1822, plain, (![A_9, A_179]: (~m1_subset_1(A_9, k1_zfmisc_1(A_179)) | ~m1_subset_1(A_9, k1_zfmisc_1(A_9)) | k3_xboole_0(A_179, A_9)=A_9)), inference(resolution, [status(thm)], [c_979, c_1794])).
% 7.09/2.45  tff(c_1918, plain, (![A_248, A_249]: (~m1_subset_1(A_248, k1_zfmisc_1(A_249)) | k3_xboole_0(A_249, A_248)=A_248)), inference(demodulation, [status(thm), theory('equality')], [c_53, c_1822])).
% 7.09/2.45  tff(c_1929, plain, (k3_xboole_0(k2_struct_0('#skF_3'), '#skF_5')='#skF_5'), inference(resolution, [status(thm)], [c_76, c_1918])).
% 7.09/2.45  tff(c_234, plain, (![A_75, B_76, C_77]: (r2_hidden('#skF_1'(A_75, B_76, C_77), A_75) | r2_hidden('#skF_2'(A_75, B_76, C_77), C_77) | k3_xboole_0(A_75, B_76)=C_77)), inference(cnfTransformation, [status(thm)], [f_34])).
% 7.09/2.45  tff(c_266, plain, (![A_78, B_79]: (r2_hidden('#skF_2'(A_78, B_79, A_78), A_78) | k3_xboole_0(A_78, B_79)=A_78)), inference(resolution, [status(thm)], [c_234, c_14])).
% 7.09/2.45  tff(c_6, plain, (![D_6, A_1, B_2]: (r2_hidden(D_6, A_1) | ~r2_hidden(D_6, k3_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 7.09/2.45  tff(c_278, plain, (![A_1, B_2, B_79]: (r2_hidden('#skF_2'(k3_xboole_0(A_1, B_2), B_79, k3_xboole_0(A_1, B_2)), A_1) | k3_xboole_0(k3_xboole_0(A_1, B_2), B_79)=k3_xboole_0(A_1, B_2))), inference(resolution, [status(thm)], [c_266, c_6])).
% 7.09/2.45  tff(c_2056, plain, (![B_79]: (r2_hidden('#skF_2'(k3_xboole_0(k2_struct_0('#skF_3'), '#skF_5'), B_79, '#skF_5'), k2_struct_0('#skF_3')) | k3_xboole_0(k3_xboole_0(k2_struct_0('#skF_3'), '#skF_5'), B_79)=k3_xboole_0(k2_struct_0('#skF_3'), '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_1929, c_278])).
% 7.09/2.45  tff(c_2225, plain, (![B_256]: (r2_hidden('#skF_2'('#skF_5', B_256, '#skF_5'), k2_struct_0('#skF_3')) | k3_xboole_0('#skF_5', B_256)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1929, c_1929, c_1929, c_2056])).
% 7.09/2.45  tff(c_16, plain, (![A_1, B_2, C_3]: (r2_hidden('#skF_1'(A_1, B_2, C_3), B_2) | r2_hidden('#skF_2'(A_1, B_2, C_3), C_3) | k3_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_34])).
% 7.09/2.45  tff(c_415, plain, (![A_116, B_117, C_118]: (r2_hidden('#skF_1'(A_116, B_117, C_118), B_117) | ~r2_hidden('#skF_2'(A_116, B_117, C_118), B_117) | ~r2_hidden('#skF_2'(A_116, B_117, C_118), A_116) | k3_xboole_0(A_116, B_117)=C_118)), inference(cnfTransformation, [status(thm)], [f_34])).
% 7.09/2.45  tff(c_442, plain, (![C_119, B_120]: (~r2_hidden('#skF_2'(C_119, B_120, C_119), B_120) | r2_hidden('#skF_1'(C_119, B_120, C_119), B_120) | k3_xboole_0(C_119, B_120)=C_119)), inference(resolution, [status(thm)], [c_16, c_415])).
% 7.09/2.45  tff(c_462, plain, (![C_119, B_120, A_9]: (r2_hidden('#skF_1'(C_119, B_120, C_119), A_9) | ~m1_subset_1(B_120, k1_zfmisc_1(A_9)) | ~r2_hidden('#skF_2'(C_119, B_120, C_119), B_120) | k3_xboole_0(C_119, B_120)=C_119)), inference(resolution, [status(thm)], [c_442, c_24])).
% 7.09/2.45  tff(c_2234, plain, (![A_9]: (r2_hidden('#skF_1'('#skF_5', k2_struct_0('#skF_3'), '#skF_5'), A_9) | ~m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(A_9)) | k3_xboole_0('#skF_5', k2_struct_0('#skF_3'))='#skF_5')), inference(resolution, [status(thm)], [c_2225, c_462])).
% 7.09/2.45  tff(c_3264, plain, (k3_xboole_0('#skF_5', k2_struct_0('#skF_3'))='#skF_5'), inference(splitLeft, [status(thm)], [c_2234])).
% 7.09/2.45  tff(c_42, plain, (v3_pre_topc('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_99])).
% 7.09/2.45  tff(c_52, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_99])).
% 7.09/2.45  tff(c_103, plain, (![A_8, B_51]: (k9_subset_1(A_8, B_51, A_8)=k3_xboole_0(B_51, A_8))), inference(resolution, [status(thm)], [c_53, c_94])).
% 7.09/2.45  tff(c_46, plain, (v1_tops_1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_99])).
% 7.09/2.45  tff(c_178, plain, (![A_64, B_65]: (k2_pre_topc(A_64, B_65)=k2_struct_0(A_64) | ~v1_tops_1(B_65, A_64) | ~m1_subset_1(B_65, k1_zfmisc_1(u1_struct_0(A_64))) | ~l1_pre_topc(A_64))), inference(cnfTransformation, [status(thm)], [f_68])).
% 7.09/2.45  tff(c_181, plain, (![B_65]: (k2_pre_topc('#skF_3', B_65)=k2_struct_0('#skF_3') | ~v1_tops_1(B_65, '#skF_3') | ~m1_subset_1(B_65, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_74, c_178])).
% 7.09/2.45  tff(c_206, plain, (![B_70]: (k2_pre_topc('#skF_3', B_70)=k2_struct_0('#skF_3') | ~v1_tops_1(B_70, '#skF_3') | ~m1_subset_1(B_70, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_181])).
% 7.09/2.45  tff(c_209, plain, (k2_pre_topc('#skF_3', '#skF_4')=k2_struct_0('#skF_3') | ~v1_tops_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_77, c_206])).
% 7.09/2.45  tff(c_219, plain, (k2_pre_topc('#skF_3', '#skF_4')=k2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_209])).
% 7.09/2.45  tff(c_609, plain, (![A_128, B_129, C_130]: (k2_pre_topc(A_128, k9_subset_1(u1_struct_0(A_128), B_129, k2_pre_topc(A_128, C_130)))=k2_pre_topc(A_128, k9_subset_1(u1_struct_0(A_128), B_129, C_130)) | ~v3_pre_topc(B_129, A_128) | ~m1_subset_1(C_130, k1_zfmisc_1(u1_struct_0(A_128))) | ~m1_subset_1(B_129, k1_zfmisc_1(u1_struct_0(A_128))) | ~l1_pre_topc(A_128) | ~v2_pre_topc(A_128))), inference(cnfTransformation, [status(thm)], [f_82])).
% 7.09/2.45  tff(c_624, plain, (![B_129]: (k2_pre_topc('#skF_3', k9_subset_1(u1_struct_0('#skF_3'), B_129, k2_struct_0('#skF_3')))=k2_pre_topc('#skF_3', k9_subset_1(u1_struct_0('#skF_3'), B_129, '#skF_4')) | ~v3_pre_topc(B_129, '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1(B_129, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_219, c_609])).
% 7.09/2.45  tff(c_877, plain, (![B_169]: (k2_pre_topc('#skF_3', k3_xboole_0(B_169, k2_struct_0('#skF_3')))=k2_pre_topc('#skF_3', k3_xboole_0(B_169, '#skF_4')) | ~v3_pre_topc(B_169, '#skF_3') | ~m1_subset_1(B_169, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_74, c_77, c_74, c_101, c_103, c_74, c_74, c_624])).
% 7.09/2.45  tff(c_883, plain, (k2_pre_topc('#skF_3', k3_xboole_0('#skF_5', k2_struct_0('#skF_3')))=k2_pre_topc('#skF_3', k3_xboole_0('#skF_5', '#skF_4')) | ~v3_pre_topc('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_76, c_877])).
% 7.09/2.45  tff(c_892, plain, (k2_pre_topc('#skF_3', k3_xboole_0('#skF_5', k2_struct_0('#skF_3')))=k2_pre_topc('#skF_3', k3_xboole_0('#skF_5', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_883])).
% 7.09/2.45  tff(c_3265, plain, (k2_pre_topc('#skF_3', k3_xboole_0('#skF_5', '#skF_4'))=k2_pre_topc('#skF_3', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_3264, c_892])).
% 7.09/2.45  tff(c_3267, plain, $false, inference(negUnitSimplification, [status(thm)], [c_113, c_3265])).
% 7.09/2.45  tff(c_3269, plain, (k3_xboole_0('#skF_5', k2_struct_0('#skF_3'))!='#skF_5'), inference(splitRight, [status(thm)], [c_2234])).
% 7.09/2.45  tff(c_2096, plain, (![B_79]: (r2_hidden('#skF_2'('#skF_5', B_79, '#skF_5'), k2_struct_0('#skF_3')) | k3_xboole_0('#skF_5', B_79)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1929, c_1929, c_1929, c_2056])).
% 7.09/2.45  tff(c_1030, plain, (![A_188, B_189, C_190, A_191]: (r2_hidden('#skF_1'(A_188, B_189, C_190), A_191) | ~m1_subset_1(A_188, k1_zfmisc_1(A_191)) | r2_hidden('#skF_2'(A_188, B_189, C_190), C_190) | k3_xboole_0(A_188, B_189)=C_190)), inference(resolution, [status(thm)], [c_234, c_24])).
% 7.09/2.45  tff(c_1074, plain, (![A_192, A_193, B_194]: (~m1_subset_1(A_192, k1_zfmisc_1(A_193)) | r2_hidden('#skF_2'(A_192, B_194, A_193), A_193) | k3_xboole_0(A_192, B_194)=A_193)), inference(resolution, [status(thm)], [c_1030, c_14])).
% 7.09/2.45  tff(c_1095, plain, (![A_192, B_194, A_193, A_9]: (r2_hidden('#skF_2'(A_192, B_194, A_193), A_9) | ~m1_subset_1(A_193, k1_zfmisc_1(A_9)) | ~m1_subset_1(A_192, k1_zfmisc_1(A_193)) | k3_xboole_0(A_192, B_194)=A_193)), inference(resolution, [status(thm)], [c_1074, c_24])).
% 7.09/2.45  tff(c_12, plain, (![A_1, B_2, C_3]: (r2_hidden('#skF_1'(A_1, B_2, C_3), A_1) | ~r2_hidden('#skF_2'(A_1, B_2, C_3), B_2) | ~r2_hidden('#skF_2'(A_1, B_2, C_3), A_1) | k3_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_34])).
% 7.09/2.45  tff(c_2235, plain, (r2_hidden('#skF_1'('#skF_5', k2_struct_0('#skF_3'), '#skF_5'), '#skF_5') | ~r2_hidden('#skF_2'('#skF_5', k2_struct_0('#skF_3'), '#skF_5'), '#skF_5') | k3_xboole_0('#skF_5', k2_struct_0('#skF_3'))='#skF_5'), inference(resolution, [status(thm)], [c_2225, c_12])).
% 7.09/2.45  tff(c_4591, plain, (r2_hidden('#skF_1'('#skF_5', k2_struct_0('#skF_3'), '#skF_5'), '#skF_5') | ~r2_hidden('#skF_2'('#skF_5', k2_struct_0('#skF_3'), '#skF_5'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_3269, c_2235])).
% 7.09/2.45  tff(c_4592, plain, (~r2_hidden('#skF_2'('#skF_5', k2_struct_0('#skF_3'), '#skF_5'), '#skF_5')), inference(splitLeft, [status(thm)], [c_4591])).
% 7.09/2.45  tff(c_4596, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_5')) | k3_xboole_0('#skF_5', k2_struct_0('#skF_3'))='#skF_5'), inference(resolution, [status(thm)], [c_1095, c_4592])).
% 7.09/2.45  tff(c_4620, plain, (k3_xboole_0('#skF_5', k2_struct_0('#skF_3'))='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_53, c_4596])).
% 7.09/2.45  tff(c_4622, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3269, c_4620])).
% 7.09/2.45  tff(c_4624, plain, (r2_hidden('#skF_2'('#skF_5', k2_struct_0('#skF_3'), '#skF_5'), '#skF_5')), inference(splitRight, [status(thm)], [c_4591])).
% 7.09/2.45  tff(c_4623, plain, (r2_hidden('#skF_1'('#skF_5', k2_struct_0('#skF_3'), '#skF_5'), '#skF_5')), inference(splitRight, [status(thm)], [c_4591])).
% 7.09/2.45  tff(c_4844, plain, (![A_393]: (r2_hidden('#skF_1'('#skF_5', k2_struct_0('#skF_3'), '#skF_5'), A_393) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_393)))), inference(resolution, [status(thm)], [c_4623, c_24])).
% 7.09/2.45  tff(c_4847, plain, (~r2_hidden('#skF_2'('#skF_5', k2_struct_0('#skF_3'), '#skF_5'), k2_struct_0('#skF_3')) | ~r2_hidden('#skF_2'('#skF_5', k2_struct_0('#skF_3'), '#skF_5'), '#skF_5') | k3_xboole_0('#skF_5', k2_struct_0('#skF_3'))='#skF_5' | ~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_5'))), inference(resolution, [status(thm)], [c_4844, c_8])).
% 7.09/2.45  tff(c_4864, plain, (~r2_hidden('#skF_2'('#skF_5', k2_struct_0('#skF_3'), '#skF_5'), k2_struct_0('#skF_3')) | k3_xboole_0('#skF_5', k2_struct_0('#skF_3'))='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_53, c_4624, c_4847])).
% 7.09/2.45  tff(c_4865, plain, (~r2_hidden('#skF_2'('#skF_5', k2_struct_0('#skF_3'), '#skF_5'), k2_struct_0('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_3269, c_4864])).
% 7.09/2.45  tff(c_4882, plain, (k3_xboole_0('#skF_5', k2_struct_0('#skF_3'))='#skF_5'), inference(resolution, [status(thm)], [c_2096, c_4865])).
% 7.09/2.45  tff(c_4916, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3269, c_4882])).
% 7.09/2.45  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.09/2.45  
% 7.09/2.45  Inference rules
% 7.09/2.45  ----------------------
% 7.09/2.45  #Ref     : 0
% 7.09/2.45  #Sup     : 1095
% 7.09/2.45  #Fact    : 0
% 7.09/2.45  #Define  : 0
% 7.09/2.45  #Split   : 9
% 7.09/2.45  #Chain   : 0
% 7.09/2.45  #Close   : 0
% 7.09/2.45  
% 7.09/2.45  Ordering : KBO
% 7.09/2.45  
% 7.09/2.45  Simplification rules
% 7.09/2.45  ----------------------
% 7.09/2.45  #Subsume      : 365
% 7.09/2.45  #Demod        : 791
% 7.09/2.45  #Tautology    : 121
% 7.09/2.45  #SimpNegUnit  : 19
% 7.09/2.45  #BackRed      : 5
% 7.09/2.45  
% 7.09/2.45  #Partial instantiations: 0
% 7.09/2.45  #Strategies tried      : 1
% 7.09/2.45  
% 7.09/2.45  Timing (in seconds)
% 7.09/2.45  ----------------------
% 7.09/2.45  Preprocessing        : 0.32
% 7.09/2.45  Parsing              : 0.16
% 7.09/2.45  CNF conversion       : 0.02
% 7.09/2.45  Main loop            : 1.34
% 7.09/2.45  Inferencing          : 0.45
% 7.09/2.45  Reduction            : 0.36
% 7.09/2.45  Demodulation         : 0.26
% 7.09/2.45  BG Simplification    : 0.05
% 7.09/2.45  Subsumption          : 0.39
% 7.09/2.45  Abstraction          : 0.07
% 7.09/2.45  MUC search           : 0.00
% 7.09/2.45  Cooper               : 0.00
% 7.09/2.45  Total                : 1.70
% 7.09/2.45  Index Insertion      : 0.00
% 7.09/2.45  Index Deletion       : 0.00
% 7.09/2.45  Index Matching       : 0.00
% 7.09/2.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
