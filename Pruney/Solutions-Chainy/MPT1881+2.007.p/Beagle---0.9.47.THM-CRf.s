%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:06 EST 2020

% Result     : Theorem 4.15s
% Output     : CNFRefutation 4.61s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 286 expanded)
%              Number of leaves         :   31 ( 110 expanded)
%              Depth                    :   12
%              Number of atoms          :  201 ( 812 expanded)
%              Number of equality atoms :   28 (  76 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_tex_2 > v2_tex_2 > v1_tops_1 > v1_subset_1 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_tdlat_3 > l1_pre_topc > k2_xboole_0 > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v1_tdlat_3,type,(
    v1_tdlat_3: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v1_tops_1,type,(
    v1_tops_1: ( $i * $i ) > $o )).

tff(v3_tex_2,type,(
    v3_tex_2: ( $i * $i ) > $o )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_33,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_38,axiom,(
    ! [A] : ~ v1_subset_1(k2_subset_1(A),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc14_subset_1)).

tff(f_143,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v1_tdlat_3(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v3_tex_2(B,A)
            <=> ~ v1_subset_1(B,u1_struct_0(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_tex_2)).

tff(f_35,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_109,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v1_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => v2_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tex_2)).

tff(f_77,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

tff(f_95,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_tex_2(B,A)
          <=> ( v2_tex_2(B,A)
              & ! [C] :
                  ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
                 => ( ( v2_tex_2(C,A)
                      & r1_tarski(B,C) )
                   => B = C ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tex_2)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_42,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(c_6,plain,(
    ! [A_5] : k2_subset_1(A_5) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [A_7] : ~ v1_subset_1(k2_subset_1(A_7),A_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_63,plain,(
    ! [A_7] : ~ v1_subset_1(A_7,A_7) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_10])).

tff(c_54,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_52,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_50,plain,(
    v1_tdlat_3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_48,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_8,plain,(
    ! [A_6] : m1_subset_1(k2_subset_1(A_6),k1_zfmisc_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_64,plain,(
    ! [A_6] : m1_subset_1(A_6,k1_zfmisc_1(A_6)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_8])).

tff(c_1757,plain,(
    ! [B_191,A_192] :
      ( v2_tex_2(B_191,A_192)
      | ~ m1_subset_1(B_191,k1_zfmisc_1(u1_struct_0(A_192)))
      | ~ l1_pre_topc(A_192)
      | ~ v1_tdlat_3(A_192)
      | ~ v2_pre_topc(A_192)
      | v2_struct_0(A_192) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_1778,plain,(
    ! [A_192] :
      ( v2_tex_2(u1_struct_0(A_192),A_192)
      | ~ l1_pre_topc(A_192)
      | ~ v1_tdlat_3(A_192)
      | ~ v2_pre_topc(A_192)
      | v2_struct_0(A_192) ) ),
    inference(resolution,[status(thm)],[c_64,c_1757])).

tff(c_46,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_56,plain,
    ( v1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ v3_tex_2('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_109,plain,(
    ~ v3_tex_2('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_62,plain,
    ( v3_tex_2('#skF_3','#skF_2')
    | ~ v1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_112,plain,(
    ~ v1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_109,c_62])).

tff(c_149,plain,(
    ! [B_52,A_53] :
      ( v1_subset_1(B_52,A_53)
      | B_52 = A_53
      | ~ m1_subset_1(B_52,k1_zfmisc_1(A_53)) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_155,plain,
    ( v1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | u1_struct_0('#skF_2') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_46,c_149])).

tff(c_162,plain,(
    u1_struct_0('#skF_2') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_112,c_155])).

tff(c_812,plain,(
    ! [B_103,A_104] :
      ( v2_tex_2(B_103,A_104)
      | ~ m1_subset_1(B_103,k1_zfmisc_1(u1_struct_0(A_104)))
      | ~ l1_pre_topc(A_104)
      | ~ v1_tdlat_3(A_104)
      | ~ v2_pre_topc(A_104)
      | v2_struct_0(A_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_818,plain,(
    ! [B_103] :
      ( v2_tex_2(B_103,'#skF_2')
      | ~ m1_subset_1(B_103,k1_zfmisc_1('#skF_3'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v1_tdlat_3('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_162,c_812])).

tff(c_829,plain,(
    ! [B_103] :
      ( v2_tex_2(B_103,'#skF_2')
      | ~ m1_subset_1(B_103,k1_zfmisc_1('#skF_3'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_818])).

tff(c_833,plain,(
    ! [B_105] :
      ( v2_tex_2(B_105,'#skF_2')
      | ~ m1_subset_1(B_105,k1_zfmisc_1('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_829])).

tff(c_847,plain,(
    v2_tex_2('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_833])).

tff(c_1039,plain,(
    ! [A_114,B_115] :
      ( '#skF_1'(A_114,B_115) != B_115
      | v3_tex_2(B_115,A_114)
      | ~ v2_tex_2(B_115,A_114)
      | ~ m1_subset_1(B_115,k1_zfmisc_1(u1_struct_0(A_114)))
      | ~ l1_pre_topc(A_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_1045,plain,(
    ! [B_115] :
      ( '#skF_1'('#skF_2',B_115) != B_115
      | v3_tex_2(B_115,'#skF_2')
      | ~ v2_tex_2(B_115,'#skF_2')
      | ~ m1_subset_1(B_115,k1_zfmisc_1('#skF_3'))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_162,c_1039])).

tff(c_1059,plain,(
    ! [B_116] :
      ( '#skF_1'('#skF_2',B_116) != B_116
      | v3_tex_2(B_116,'#skF_2')
      | ~ v2_tex_2(B_116,'#skF_2')
      | ~ m1_subset_1(B_116,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1045])).

tff(c_1070,plain,
    ( '#skF_1'('#skF_2','#skF_3') != '#skF_3'
    | v3_tex_2('#skF_3','#skF_2')
    | ~ v2_tex_2('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_1059])).

tff(c_1075,plain,
    ( '#skF_1'('#skF_2','#skF_3') != '#skF_3'
    | v3_tex_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_847,c_1070])).

tff(c_1076,plain,(
    '#skF_1'('#skF_2','#skF_3') != '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_109,c_1075])).

tff(c_1196,plain,(
    ! [B_126,A_127] :
      ( r1_tarski(B_126,'#skF_1'(A_127,B_126))
      | v3_tex_2(B_126,A_127)
      | ~ v2_tex_2(B_126,A_127)
      | ~ m1_subset_1(B_126,k1_zfmisc_1(u1_struct_0(A_127)))
      | ~ l1_pre_topc(A_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_1200,plain,(
    ! [B_126] :
      ( r1_tarski(B_126,'#skF_1'('#skF_2',B_126))
      | v3_tex_2(B_126,'#skF_2')
      | ~ v2_tex_2(B_126,'#skF_2')
      | ~ m1_subset_1(B_126,k1_zfmisc_1('#skF_3'))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_162,c_1196])).

tff(c_1212,plain,(
    ! [B_128] :
      ( r1_tarski(B_128,'#skF_1'('#skF_2',B_128))
      | v3_tex_2(B_128,'#skF_2')
      | ~ v2_tex_2(B_128,'#skF_2')
      | ~ m1_subset_1(B_128,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1200])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k2_xboole_0(A_3,B_4) = B_4
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1241,plain,(
    ! [B_132] :
      ( k2_xboole_0(B_132,'#skF_1'('#skF_2',B_132)) = '#skF_1'('#skF_2',B_132)
      | v3_tex_2(B_132,'#skF_2')
      | ~ v2_tex_2(B_132,'#skF_2')
      | ~ m1_subset_1(B_132,k1_zfmisc_1('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_1212,c_4])).

tff(c_1249,plain,
    ( k2_xboole_0('#skF_3','#skF_1'('#skF_2','#skF_3')) = '#skF_1'('#skF_2','#skF_3')
    | v3_tex_2('#skF_3','#skF_2')
    | ~ v2_tex_2('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_1241])).

tff(c_1254,plain,
    ( k2_xboole_0('#skF_3','#skF_1'('#skF_2','#skF_3')) = '#skF_1'('#skF_2','#skF_3')
    | v3_tex_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_847,c_1249])).

tff(c_1255,plain,(
    k2_xboole_0('#skF_3','#skF_1'('#skF_2','#skF_3')) = '#skF_1'('#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_109,c_1254])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_1381,plain,(
    ! [A_146,B_147] :
      ( m1_subset_1('#skF_1'(A_146,B_147),k1_zfmisc_1(u1_struct_0(A_146)))
      | v3_tex_2(B_147,A_146)
      | ~ v2_tex_2(B_147,A_146)
      | ~ m1_subset_1(B_147,k1_zfmisc_1(u1_struct_0(A_146)))
      | ~ l1_pre_topc(A_146) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_1413,plain,(
    ! [B_147] :
      ( m1_subset_1('#skF_1'('#skF_2',B_147),k1_zfmisc_1('#skF_3'))
      | v3_tex_2(B_147,'#skF_2')
      | ~ v2_tex_2(B_147,'#skF_2')
      | ~ m1_subset_1(B_147,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_162,c_1381])).

tff(c_1427,plain,(
    ! [B_148] :
      ( m1_subset_1('#skF_1'('#skF_2',B_148),k1_zfmisc_1('#skF_3'))
      | v3_tex_2(B_148,'#skF_2')
      | ~ v2_tex_2(B_148,'#skF_2')
      | ~ m1_subset_1(B_148,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_162,c_1413])).

tff(c_12,plain,(
    ! [A_8,B_9] :
      ( r1_tarski(A_8,B_9)
      | ~ m1_subset_1(A_8,k1_zfmisc_1(B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1462,plain,(
    ! [B_149] :
      ( r1_tarski('#skF_1'('#skF_2',B_149),'#skF_3')
      | v3_tex_2(B_149,'#skF_2')
      | ~ v2_tex_2(B_149,'#skF_2')
      | ~ m1_subset_1(B_149,k1_zfmisc_1('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_1427,c_12])).

tff(c_1465,plain,(
    ! [B_149] :
      ( k2_xboole_0('#skF_1'('#skF_2',B_149),'#skF_3') = '#skF_3'
      | v3_tex_2(B_149,'#skF_2')
      | ~ v2_tex_2(B_149,'#skF_2')
      | ~ m1_subset_1(B_149,k1_zfmisc_1('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_1462,c_4])).

tff(c_1468,plain,(
    ! [B_150] :
      ( k2_xboole_0('#skF_3','#skF_1'('#skF_2',B_150)) = '#skF_3'
      | v3_tex_2(B_150,'#skF_2')
      | ~ v2_tex_2(B_150,'#skF_2')
      | ~ m1_subset_1(B_150,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_1465])).

tff(c_1482,plain,
    ( k2_xboole_0('#skF_3','#skF_1'('#skF_2','#skF_3')) = '#skF_3'
    | v3_tex_2('#skF_3','#skF_2')
    | ~ v2_tex_2('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_1468])).

tff(c_1488,plain,
    ( '#skF_1'('#skF_2','#skF_3') = '#skF_3'
    | v3_tex_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_847,c_1255,c_1482])).

tff(c_1490,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_109,c_1076,c_1488])).

tff(c_1492,plain,(
    v3_tex_2('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_1503,plain,(
    ! [A_156,B_157] :
      ( r1_tarski(A_156,B_157)
      | ~ m1_subset_1(A_156,k1_zfmisc_1(B_157)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1514,plain,(
    r1_tarski('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_46,c_1503])).

tff(c_2208,plain,(
    ! [C_231,B_232,A_233] :
      ( C_231 = B_232
      | ~ r1_tarski(B_232,C_231)
      | ~ v2_tex_2(C_231,A_233)
      | ~ m1_subset_1(C_231,k1_zfmisc_1(u1_struct_0(A_233)))
      | ~ v3_tex_2(B_232,A_233)
      | ~ m1_subset_1(B_232,k1_zfmisc_1(u1_struct_0(A_233)))
      | ~ l1_pre_topc(A_233) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_2234,plain,(
    ! [A_233] :
      ( u1_struct_0('#skF_2') = '#skF_3'
      | ~ v2_tex_2(u1_struct_0('#skF_2'),A_233)
      | ~ m1_subset_1(u1_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_233)))
      | ~ v3_tex_2('#skF_3',A_233)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_233)))
      | ~ l1_pre_topc(A_233) ) ),
    inference(resolution,[status(thm)],[c_1514,c_2208])).

tff(c_2523,plain,(
    ! [A_252] :
      ( ~ v2_tex_2(u1_struct_0('#skF_2'),A_252)
      | ~ m1_subset_1(u1_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_252)))
      | ~ v3_tex_2('#skF_3',A_252)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_252)))
      | ~ l1_pre_topc(A_252) ) ),
    inference(splitLeft,[status(thm)],[c_2234])).

tff(c_2530,plain,
    ( ~ v2_tex_2(u1_struct_0('#skF_2'),'#skF_2')
    | ~ v3_tex_2('#skF_3','#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_2523])).

tff(c_2534,plain,(
    ~ v2_tex_2(u1_struct_0('#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_1492,c_2530])).

tff(c_2537,plain,
    ( ~ l1_pre_topc('#skF_2')
    | ~ v1_tdlat_3('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_1778,c_2534])).

tff(c_2540,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_2537])).

tff(c_2542,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_2540])).

tff(c_2543,plain,(
    u1_struct_0('#skF_2') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_2234])).

tff(c_1491,plain,(
    v1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_2548,plain,(
    v1_subset_1('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2543,c_1491])).

tff(c_2553,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_63,c_2548])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.32  % Computer   : n023.cluster.edu
% 0.14/0.32  % Model      : x86_64 x86_64
% 0.14/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.32  % Memory     : 8042.1875MB
% 0.14/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 17:34:20 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.15/1.76  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.53/1.77  
% 4.53/1.77  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.53/1.77  %$ v3_tex_2 > v2_tex_2 > v1_tops_1 > v1_subset_1 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_tdlat_3 > l1_pre_topc > k2_xboole_0 > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 4.53/1.77  
% 4.53/1.77  %Foreground sorts:
% 4.53/1.77  
% 4.53/1.77  
% 4.53/1.77  %Background operators:
% 4.53/1.77  
% 4.53/1.77  
% 4.53/1.77  %Foreground operators:
% 4.53/1.77  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.53/1.77  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.53/1.77  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 4.53/1.77  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.53/1.77  tff(v1_tdlat_3, type, v1_tdlat_3: $i > $o).
% 4.53/1.77  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.53/1.77  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 4.53/1.77  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 4.53/1.77  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 4.53/1.77  tff('#skF_2', type, '#skF_2': $i).
% 4.53/1.77  tff('#skF_3', type, '#skF_3': $i).
% 4.53/1.77  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.53/1.77  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.53/1.77  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.53/1.77  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.53/1.77  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.53/1.77  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.53/1.77  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.53/1.77  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 4.53/1.77  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 4.53/1.77  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.53/1.77  
% 4.61/1.79  tff(f_33, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 4.61/1.79  tff(f_38, axiom, (![A]: ~v1_subset_1(k2_subset_1(A), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc14_subset_1)).
% 4.61/1.79  tff(f_143, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> ~v1_subset_1(B, u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_tex_2)).
% 4.61/1.79  tff(f_35, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 4.61/1.79  tff(f_109, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_tex_2)).
% 4.61/1.79  tff(f_77, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_subset_1)).
% 4.61/1.79  tff(f_95, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> (v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(C, A) & r1_tarski(B, C)) => (B = C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_tex_2)).
% 4.61/1.79  tff(f_31, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 4.61/1.79  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 4.61/1.79  tff(f_42, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 4.61/1.79  tff(c_6, plain, (![A_5]: (k2_subset_1(A_5)=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.61/1.79  tff(c_10, plain, (![A_7]: (~v1_subset_1(k2_subset_1(A_7), A_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.61/1.79  tff(c_63, plain, (![A_7]: (~v1_subset_1(A_7, A_7))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_10])).
% 4.61/1.79  tff(c_54, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_143])).
% 4.61/1.79  tff(c_52, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_143])).
% 4.61/1.79  tff(c_50, plain, (v1_tdlat_3('#skF_2')), inference(cnfTransformation, [status(thm)], [f_143])).
% 4.61/1.79  tff(c_48, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_143])).
% 4.61/1.79  tff(c_8, plain, (![A_6]: (m1_subset_1(k2_subset_1(A_6), k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.61/1.79  tff(c_64, plain, (![A_6]: (m1_subset_1(A_6, k1_zfmisc_1(A_6)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_8])).
% 4.61/1.79  tff(c_1757, plain, (![B_191, A_192]: (v2_tex_2(B_191, A_192) | ~m1_subset_1(B_191, k1_zfmisc_1(u1_struct_0(A_192))) | ~l1_pre_topc(A_192) | ~v1_tdlat_3(A_192) | ~v2_pre_topc(A_192) | v2_struct_0(A_192))), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.61/1.79  tff(c_1778, plain, (![A_192]: (v2_tex_2(u1_struct_0(A_192), A_192) | ~l1_pre_topc(A_192) | ~v1_tdlat_3(A_192) | ~v2_pre_topc(A_192) | v2_struct_0(A_192))), inference(resolution, [status(thm)], [c_64, c_1757])).
% 4.61/1.79  tff(c_46, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_143])).
% 4.61/1.79  tff(c_56, plain, (v1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~v3_tex_2('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_143])).
% 4.61/1.79  tff(c_109, plain, (~v3_tex_2('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_56])).
% 4.61/1.79  tff(c_62, plain, (v3_tex_2('#skF_3', '#skF_2') | ~v1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_143])).
% 4.61/1.79  tff(c_112, plain, (~v1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_109, c_62])).
% 4.61/1.79  tff(c_149, plain, (![B_52, A_53]: (v1_subset_1(B_52, A_53) | B_52=A_53 | ~m1_subset_1(B_52, k1_zfmisc_1(A_53)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.61/1.79  tff(c_155, plain, (v1_subset_1('#skF_3', u1_struct_0('#skF_2')) | u1_struct_0('#skF_2')='#skF_3'), inference(resolution, [status(thm)], [c_46, c_149])).
% 4.61/1.79  tff(c_162, plain, (u1_struct_0('#skF_2')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_112, c_155])).
% 4.61/1.79  tff(c_812, plain, (![B_103, A_104]: (v2_tex_2(B_103, A_104) | ~m1_subset_1(B_103, k1_zfmisc_1(u1_struct_0(A_104))) | ~l1_pre_topc(A_104) | ~v1_tdlat_3(A_104) | ~v2_pre_topc(A_104) | v2_struct_0(A_104))), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.61/1.79  tff(c_818, plain, (![B_103]: (v2_tex_2(B_103, '#skF_2') | ~m1_subset_1(B_103, k1_zfmisc_1('#skF_3')) | ~l1_pre_topc('#skF_2') | ~v1_tdlat_3('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_162, c_812])).
% 4.61/1.79  tff(c_829, plain, (![B_103]: (v2_tex_2(B_103, '#skF_2') | ~m1_subset_1(B_103, k1_zfmisc_1('#skF_3')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_818])).
% 4.61/1.79  tff(c_833, plain, (![B_105]: (v2_tex_2(B_105, '#skF_2') | ~m1_subset_1(B_105, k1_zfmisc_1('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_54, c_829])).
% 4.61/1.79  tff(c_847, plain, (v2_tex_2('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_64, c_833])).
% 4.61/1.79  tff(c_1039, plain, (![A_114, B_115]: ('#skF_1'(A_114, B_115)!=B_115 | v3_tex_2(B_115, A_114) | ~v2_tex_2(B_115, A_114) | ~m1_subset_1(B_115, k1_zfmisc_1(u1_struct_0(A_114))) | ~l1_pre_topc(A_114))), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.61/1.79  tff(c_1045, plain, (![B_115]: ('#skF_1'('#skF_2', B_115)!=B_115 | v3_tex_2(B_115, '#skF_2') | ~v2_tex_2(B_115, '#skF_2') | ~m1_subset_1(B_115, k1_zfmisc_1('#skF_3')) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_162, c_1039])).
% 4.61/1.79  tff(c_1059, plain, (![B_116]: ('#skF_1'('#skF_2', B_116)!=B_116 | v3_tex_2(B_116, '#skF_2') | ~v2_tex_2(B_116, '#skF_2') | ~m1_subset_1(B_116, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_1045])).
% 4.61/1.79  tff(c_1070, plain, ('#skF_1'('#skF_2', '#skF_3')!='#skF_3' | v3_tex_2('#skF_3', '#skF_2') | ~v2_tex_2('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_64, c_1059])).
% 4.61/1.79  tff(c_1075, plain, ('#skF_1'('#skF_2', '#skF_3')!='#skF_3' | v3_tex_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_847, c_1070])).
% 4.61/1.79  tff(c_1076, plain, ('#skF_1'('#skF_2', '#skF_3')!='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_109, c_1075])).
% 4.61/1.79  tff(c_1196, plain, (![B_126, A_127]: (r1_tarski(B_126, '#skF_1'(A_127, B_126)) | v3_tex_2(B_126, A_127) | ~v2_tex_2(B_126, A_127) | ~m1_subset_1(B_126, k1_zfmisc_1(u1_struct_0(A_127))) | ~l1_pre_topc(A_127))), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.61/1.79  tff(c_1200, plain, (![B_126]: (r1_tarski(B_126, '#skF_1'('#skF_2', B_126)) | v3_tex_2(B_126, '#skF_2') | ~v2_tex_2(B_126, '#skF_2') | ~m1_subset_1(B_126, k1_zfmisc_1('#skF_3')) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_162, c_1196])).
% 4.61/1.79  tff(c_1212, plain, (![B_128]: (r1_tarski(B_128, '#skF_1'('#skF_2', B_128)) | v3_tex_2(B_128, '#skF_2') | ~v2_tex_2(B_128, '#skF_2') | ~m1_subset_1(B_128, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_1200])).
% 4.61/1.79  tff(c_4, plain, (![A_3, B_4]: (k2_xboole_0(A_3, B_4)=B_4 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.61/1.79  tff(c_1241, plain, (![B_132]: (k2_xboole_0(B_132, '#skF_1'('#skF_2', B_132))='#skF_1'('#skF_2', B_132) | v3_tex_2(B_132, '#skF_2') | ~v2_tex_2(B_132, '#skF_2') | ~m1_subset_1(B_132, k1_zfmisc_1('#skF_3')))), inference(resolution, [status(thm)], [c_1212, c_4])).
% 4.61/1.79  tff(c_1249, plain, (k2_xboole_0('#skF_3', '#skF_1'('#skF_2', '#skF_3'))='#skF_1'('#skF_2', '#skF_3') | v3_tex_2('#skF_3', '#skF_2') | ~v2_tex_2('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_64, c_1241])).
% 4.61/1.79  tff(c_1254, plain, (k2_xboole_0('#skF_3', '#skF_1'('#skF_2', '#skF_3'))='#skF_1'('#skF_2', '#skF_3') | v3_tex_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_847, c_1249])).
% 4.61/1.79  tff(c_1255, plain, (k2_xboole_0('#skF_3', '#skF_1'('#skF_2', '#skF_3'))='#skF_1'('#skF_2', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_109, c_1254])).
% 4.61/1.79  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.61/1.79  tff(c_1381, plain, (![A_146, B_147]: (m1_subset_1('#skF_1'(A_146, B_147), k1_zfmisc_1(u1_struct_0(A_146))) | v3_tex_2(B_147, A_146) | ~v2_tex_2(B_147, A_146) | ~m1_subset_1(B_147, k1_zfmisc_1(u1_struct_0(A_146))) | ~l1_pre_topc(A_146))), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.61/1.79  tff(c_1413, plain, (![B_147]: (m1_subset_1('#skF_1'('#skF_2', B_147), k1_zfmisc_1('#skF_3')) | v3_tex_2(B_147, '#skF_2') | ~v2_tex_2(B_147, '#skF_2') | ~m1_subset_1(B_147, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_162, c_1381])).
% 4.61/1.79  tff(c_1427, plain, (![B_148]: (m1_subset_1('#skF_1'('#skF_2', B_148), k1_zfmisc_1('#skF_3')) | v3_tex_2(B_148, '#skF_2') | ~v2_tex_2(B_148, '#skF_2') | ~m1_subset_1(B_148, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_162, c_1413])).
% 4.61/1.79  tff(c_12, plain, (![A_8, B_9]: (r1_tarski(A_8, B_9) | ~m1_subset_1(A_8, k1_zfmisc_1(B_9)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.61/1.79  tff(c_1462, plain, (![B_149]: (r1_tarski('#skF_1'('#skF_2', B_149), '#skF_3') | v3_tex_2(B_149, '#skF_2') | ~v2_tex_2(B_149, '#skF_2') | ~m1_subset_1(B_149, k1_zfmisc_1('#skF_3')))), inference(resolution, [status(thm)], [c_1427, c_12])).
% 4.61/1.79  tff(c_1465, plain, (![B_149]: (k2_xboole_0('#skF_1'('#skF_2', B_149), '#skF_3')='#skF_3' | v3_tex_2(B_149, '#skF_2') | ~v2_tex_2(B_149, '#skF_2') | ~m1_subset_1(B_149, k1_zfmisc_1('#skF_3')))), inference(resolution, [status(thm)], [c_1462, c_4])).
% 4.61/1.79  tff(c_1468, plain, (![B_150]: (k2_xboole_0('#skF_3', '#skF_1'('#skF_2', B_150))='#skF_3' | v3_tex_2(B_150, '#skF_2') | ~v2_tex_2(B_150, '#skF_2') | ~m1_subset_1(B_150, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_1465])).
% 4.61/1.79  tff(c_1482, plain, (k2_xboole_0('#skF_3', '#skF_1'('#skF_2', '#skF_3'))='#skF_3' | v3_tex_2('#skF_3', '#skF_2') | ~v2_tex_2('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_64, c_1468])).
% 4.61/1.79  tff(c_1488, plain, ('#skF_1'('#skF_2', '#skF_3')='#skF_3' | v3_tex_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_847, c_1255, c_1482])).
% 4.61/1.79  tff(c_1490, plain, $false, inference(negUnitSimplification, [status(thm)], [c_109, c_1076, c_1488])).
% 4.61/1.79  tff(c_1492, plain, (v3_tex_2('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_56])).
% 4.61/1.79  tff(c_1503, plain, (![A_156, B_157]: (r1_tarski(A_156, B_157) | ~m1_subset_1(A_156, k1_zfmisc_1(B_157)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.61/1.79  tff(c_1514, plain, (r1_tarski('#skF_3', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_46, c_1503])).
% 4.61/1.79  tff(c_2208, plain, (![C_231, B_232, A_233]: (C_231=B_232 | ~r1_tarski(B_232, C_231) | ~v2_tex_2(C_231, A_233) | ~m1_subset_1(C_231, k1_zfmisc_1(u1_struct_0(A_233))) | ~v3_tex_2(B_232, A_233) | ~m1_subset_1(B_232, k1_zfmisc_1(u1_struct_0(A_233))) | ~l1_pre_topc(A_233))), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.61/1.79  tff(c_2234, plain, (![A_233]: (u1_struct_0('#skF_2')='#skF_3' | ~v2_tex_2(u1_struct_0('#skF_2'), A_233) | ~m1_subset_1(u1_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0(A_233))) | ~v3_tex_2('#skF_3', A_233) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_233))) | ~l1_pre_topc(A_233))), inference(resolution, [status(thm)], [c_1514, c_2208])).
% 4.61/1.79  tff(c_2523, plain, (![A_252]: (~v2_tex_2(u1_struct_0('#skF_2'), A_252) | ~m1_subset_1(u1_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0(A_252))) | ~v3_tex_2('#skF_3', A_252) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_252))) | ~l1_pre_topc(A_252))), inference(splitLeft, [status(thm)], [c_2234])).
% 4.61/1.79  tff(c_2530, plain, (~v2_tex_2(u1_struct_0('#skF_2'), '#skF_2') | ~v3_tex_2('#skF_3', '#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_64, c_2523])).
% 4.61/1.79  tff(c_2534, plain, (~v2_tex_2(u1_struct_0('#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_1492, c_2530])).
% 4.61/1.79  tff(c_2537, plain, (~l1_pre_topc('#skF_2') | ~v1_tdlat_3('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_1778, c_2534])).
% 4.61/1.79  tff(c_2540, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_2537])).
% 4.61/1.79  tff(c_2542, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_2540])).
% 4.61/1.79  tff(c_2543, plain, (u1_struct_0('#skF_2')='#skF_3'), inference(splitRight, [status(thm)], [c_2234])).
% 4.61/1.79  tff(c_1491, plain, (v1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_56])).
% 4.61/1.79  tff(c_2548, plain, (v1_subset_1('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2543, c_1491])).
% 4.61/1.79  tff(c_2553, plain, $false, inference(negUnitSimplification, [status(thm)], [c_63, c_2548])).
% 4.61/1.79  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.61/1.79  
% 4.61/1.79  Inference rules
% 4.61/1.79  ----------------------
% 4.61/1.79  #Ref     : 0
% 4.61/1.79  #Sup     : 523
% 4.61/1.79  #Fact    : 0
% 4.61/1.79  #Define  : 0
% 4.61/1.79  #Split   : 4
% 4.61/1.79  #Chain   : 0
% 4.61/1.79  #Close   : 0
% 4.61/1.79  
% 4.61/1.79  Ordering : KBO
% 4.61/1.79  
% 4.61/1.79  Simplification rules
% 4.61/1.79  ----------------------
% 4.61/1.79  #Subsume      : 105
% 4.61/1.79  #Demod        : 572
% 4.61/1.79  #Tautology    : 223
% 4.61/1.79  #SimpNegUnit  : 30
% 4.61/1.79  #BackRed      : 13
% 4.61/1.79  
% 4.61/1.79  #Partial instantiations: 0
% 4.61/1.79  #Strategies tried      : 1
% 4.61/1.79  
% 4.61/1.79  Timing (in seconds)
% 4.61/1.79  ----------------------
% 4.61/1.79  Preprocessing        : 0.34
% 4.61/1.79  Parsing              : 0.18
% 4.61/1.79  CNF conversion       : 0.02
% 4.61/1.79  Main loop            : 0.69
% 4.61/1.79  Inferencing          : 0.26
% 4.61/1.79  Reduction            : 0.23
% 4.61/1.79  Demodulation         : 0.16
% 4.61/1.79  BG Simplification    : 0.03
% 4.61/1.79  Subsumption          : 0.13
% 4.61/1.79  Abstraction          : 0.04
% 4.61/1.79  MUC search           : 0.00
% 4.61/1.79  Cooper               : 0.00
% 4.61/1.79  Total                : 1.07
% 4.61/1.79  Index Insertion      : 0.00
% 4.61/1.79  Index Deletion       : 0.00
% 4.61/1.79  Index Matching       : 0.00
% 4.61/1.79  BG Taut test         : 0.00
%------------------------------------------------------------------------------
