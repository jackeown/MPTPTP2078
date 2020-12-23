%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:03 EST 2020

% Result     : Theorem 33.61s
% Output     : CNFRefutation 33.97s
% Verified   : 
% Statistics : Number of formulae       :  301 (2181 expanded)
%              Number of leaves         :   31 ( 654 expanded)
%              Depth                    :   17
%              Number of atoms          :  675 (6469 expanded)
%              Number of equality atoms :   24 ( 319 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_compts_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > l1_pre_topc > k1_pre_topc > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_subset_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k1_pre_topc,type,(
    k1_pre_topc: ( $i * $i ) > $i )).

tff(v2_compts_1,type,(
    v2_compts_1: ( $i * $i ) > $o )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(g1_pre_topc,type,(
    g1_pre_topc: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_121,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( v2_compts_1(B,A)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
          <=> ( v2_compts_1(B,g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A))))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_compts_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ( v1_pre_topc(k1_pre_topc(A,B))
        & m1_pre_topc(k1_pre_topc(A,B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_pre_topc)).

tff(f_50,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_87,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ( m1_pre_topc(A,B)
          <=> m1_pre_topc(A,g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_pre_topc)).

tff(f_54,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_subset_1(u1_pre_topc(A),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( v1_pre_topc(g1_pre_topc(A,B))
        & l1_pre_topc(g1_pre_topc(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_g1_pre_topc)).

tff(f_71,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B)))
             => m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_pre_topc)).

tff(f_104,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ! [D] :
                  ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(B)))
                 => ( C = D
                   => ( v2_compts_1(C,A)
                    <=> v2_compts_1(D,B) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_compts_1)).

tff(f_27,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_29,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_61,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => u1_struct_0(k1_pre_topc(A,B)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_pre_topc)).

tff(f_78,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
         => m1_pre_topc(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_pre_topc)).

tff(c_32,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_48,plain,
    ( v2_compts_1('#skF_2',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_106,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( m1_pre_topc(k1_pre_topc(A_5,B_6),A_5)
      | ~ m1_subset_1(B_6,k1_zfmisc_1(u1_struct_0(A_5)))
      | ~ l1_pre_topc(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_108,plain,
    ( m1_pre_topc(k1_pre_topc('#skF_1','#skF_3'),'#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_106,c_10])).

tff(c_114,plain,(
    m1_pre_topc(k1_pre_topc('#skF_1','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_108])).

tff(c_14,plain,(
    ! [B_9,A_7] :
      ( l1_pre_topc(B_9)
      | ~ m1_pre_topc(B_9,A_7)
      | ~ l1_pre_topc(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_120,plain,
    ( l1_pre_topc(k1_pre_topc('#skF_1','#skF_3'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_114,c_14])).

tff(c_123,plain,(
    l1_pre_topc(k1_pre_topc('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_120])).

tff(c_26,plain,(
    ! [A_24,B_26] :
      ( m1_pre_topc(A_24,g1_pre_topc(u1_struct_0(B_26),u1_pre_topc(B_26)))
      | ~ m1_pre_topc(A_24,B_26)
      | ~ l1_pre_topc(B_26)
      | ~ l1_pre_topc(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_82,plain,(
    ! [A_53] :
      ( m1_subset_1(u1_pre_topc(A_53),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_53))))
      | ~ l1_pre_topc(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( l1_pre_topc(g1_pre_topc(A_3,B_4))
      | ~ m1_subset_1(B_4,k1_zfmisc_1(k1_zfmisc_1(A_3))) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_90,plain,(
    ! [A_53] :
      ( l1_pre_topc(g1_pre_topc(u1_struct_0(A_53),u1_pre_topc(A_53)))
      | ~ l1_pre_topc(A_53) ) ),
    inference(resolution,[status(thm)],[c_82,c_6])).

tff(c_59001,plain,(
    ! [C_701,A_702,B_703] :
      ( m1_subset_1(C_701,k1_zfmisc_1(u1_struct_0(A_702)))
      | ~ m1_subset_1(C_701,k1_zfmisc_1(u1_struct_0(B_703)))
      | ~ m1_pre_topc(B_703,A_702)
      | ~ l1_pre_topc(A_702) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_59021,plain,(
    ! [A_704] :
      ( m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_704)))
      | ~ m1_pre_topc('#skF_1',A_704)
      | ~ l1_pre_topc(A_704) ) ),
    inference(resolution,[status(thm)],[c_106,c_59001])).

tff(c_555,plain,(
    ! [C_72,A_73,B_74] :
      ( m1_subset_1(C_72,k1_zfmisc_1(u1_struct_0(A_73)))
      | ~ m1_subset_1(C_72,k1_zfmisc_1(u1_struct_0(B_74)))
      | ~ m1_pre_topc(B_74,A_73)
      | ~ l1_pre_topc(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_573,plain,(
    ! [A_73] :
      ( m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_73)))
      | ~ m1_pre_topc('#skF_1',A_73)
      | ~ l1_pre_topc(A_73) ) ),
    inference(resolution,[status(thm)],[c_106,c_555])).

tff(c_54,plain,
    ( v2_compts_1('#skF_2',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | v2_compts_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_80,plain,(
    v2_compts_1('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_1174,plain,(
    ! [D_98,A_99,B_100] :
      ( v2_compts_1(D_98,A_99)
      | ~ v2_compts_1(D_98,B_100)
      | ~ m1_subset_1(D_98,k1_zfmisc_1(u1_struct_0(B_100)))
      | ~ m1_subset_1(D_98,k1_zfmisc_1(u1_struct_0(A_99)))
      | ~ m1_pre_topc(B_100,A_99)
      | ~ l1_pre_topc(A_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_1198,plain,(
    ! [A_99] :
      ( v2_compts_1('#skF_3',A_99)
      | ~ v2_compts_1('#skF_3','#skF_1')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_99)))
      | ~ m1_pre_topc('#skF_1',A_99)
      | ~ l1_pre_topc(A_99) ) ),
    inference(resolution,[status(thm)],[c_106,c_1174])).

tff(c_1228,plain,(
    ! [A_103] :
      ( v2_compts_1('#skF_3',A_103)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_103)))
      | ~ m1_pre_topc('#skF_1',A_103)
      | ~ l1_pre_topc(A_103) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_1198])).

tff(c_1277,plain,(
    ! [A_104] :
      ( v2_compts_1('#skF_3',A_104)
      | ~ m1_pre_topc('#skF_1',A_104)
      | ~ l1_pre_topc(A_104) ) ),
    inference(resolution,[status(thm)],[c_573,c_1228])).

tff(c_42,plain,
    ( v2_compts_1('#skF_2',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))
    | ~ v2_compts_1('#skF_3',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_423,plain,(
    ~ v2_compts_1('#skF_3',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_1281,plain,
    ( ~ m1_pre_topc('#skF_1',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_1277,c_423])).

tff(c_1344,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_1281])).

tff(c_1347,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_90,c_1344])).

tff(c_1351,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1347])).

tff(c_1353,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_1281])).

tff(c_2,plain,(
    ! [A_1] : k2_subset_1(A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2] : m1_subset_1(k2_subset_1(A_2),k1_zfmisc_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_55,plain,(
    ! [A_2] : m1_subset_1(A_2,k1_zfmisc_1(A_2)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_4])).

tff(c_136,plain,(
    ! [A_65,B_66] :
      ( u1_struct_0(k1_pre_topc(A_65,B_66)) = B_66
      | ~ m1_subset_1(B_66,k1_zfmisc_1(u1_struct_0(A_65)))
      | ~ l1_pre_topc(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_139,plain,
    ( u1_struct_0(k1_pre_topc('#skF_1','#skF_3')) = '#skF_3'
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_106,c_136])).

tff(c_146,plain,(
    u1_struct_0(k1_pre_topc('#skF_1','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_139])).

tff(c_567,plain,(
    ! [C_72,A_73] :
      ( m1_subset_1(C_72,k1_zfmisc_1(u1_struct_0(A_73)))
      | ~ m1_subset_1(C_72,k1_zfmisc_1('#skF_3'))
      | ~ m1_pre_topc(k1_pre_topc('#skF_1','#skF_3'),A_73)
      | ~ l1_pre_topc(A_73) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_146,c_555])).

tff(c_574,plain,(
    ! [B_74,A_73] :
      ( m1_subset_1(u1_struct_0(B_74),k1_zfmisc_1(u1_struct_0(A_73)))
      | ~ m1_pre_topc(B_74,A_73)
      | ~ l1_pre_topc(A_73) ) ),
    inference(resolution,[status(thm)],[c_55,c_555])).

tff(c_855,plain,(
    ! [D_85,B_86,A_87] :
      ( v2_compts_1(D_85,B_86)
      | ~ v2_compts_1(D_85,A_87)
      | ~ m1_subset_1(D_85,k1_zfmisc_1(u1_struct_0(B_86)))
      | ~ m1_subset_1(D_85,k1_zfmisc_1(u1_struct_0(A_87)))
      | ~ m1_pre_topc(B_86,A_87)
      | ~ l1_pre_topc(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_1367,plain,(
    ! [B_109,A_110] :
      ( v2_compts_1(u1_struct_0(B_109),B_109)
      | ~ v2_compts_1(u1_struct_0(B_109),A_110)
      | ~ m1_subset_1(u1_struct_0(B_109),k1_zfmisc_1(u1_struct_0(A_110)))
      | ~ m1_pre_topc(B_109,A_110)
      | ~ l1_pre_topc(A_110) ) ),
    inference(resolution,[status(thm)],[c_55,c_855])).

tff(c_1420,plain,(
    ! [B_112,A_113] :
      ( v2_compts_1(u1_struct_0(B_112),B_112)
      | ~ v2_compts_1(u1_struct_0(B_112),A_113)
      | ~ m1_pre_topc(B_112,A_113)
      | ~ l1_pre_topc(A_113) ) ),
    inference(resolution,[status(thm)],[c_574,c_1367])).

tff(c_1436,plain,(
    ! [A_113] :
      ( v2_compts_1(u1_struct_0(k1_pre_topc('#skF_1','#skF_3')),k1_pre_topc('#skF_1','#skF_3'))
      | ~ v2_compts_1('#skF_3',A_113)
      | ~ m1_pre_topc(k1_pre_topc('#skF_1','#skF_3'),A_113)
      | ~ l1_pre_topc(A_113) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_146,c_1420])).

tff(c_1440,plain,(
    ! [A_113] :
      ( v2_compts_1('#skF_3',k1_pre_topc('#skF_1','#skF_3'))
      | ~ v2_compts_1('#skF_3',A_113)
      | ~ m1_pre_topc(k1_pre_topc('#skF_1','#skF_3'),A_113)
      | ~ l1_pre_topc(A_113) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_1436])).

tff(c_3172,plain,(
    ! [A_145] :
      ( ~ v2_compts_1('#skF_3',A_145)
      | ~ m1_pre_topc(k1_pre_topc('#skF_1','#skF_3'),A_145)
      | ~ l1_pre_topc(A_145) ) ),
    inference(splitLeft,[status(thm)],[c_1440])).

tff(c_3187,plain,
    ( ~ v2_compts_1('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_114,c_3172])).

tff(c_3200,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_80,c_3187])).

tff(c_3201,plain,(
    v2_compts_1('#skF_3',k1_pre_topc('#skF_1','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1440])).

tff(c_1313,plain,(
    ! [B_106,A_107] :
      ( v2_compts_1(u1_struct_0(B_106),A_107)
      | ~ v2_compts_1(u1_struct_0(B_106),B_106)
      | ~ m1_subset_1(u1_struct_0(B_106),k1_zfmisc_1(u1_struct_0(A_107)))
      | ~ m1_pre_topc(B_106,A_107)
      | ~ l1_pre_topc(A_107) ) ),
    inference(resolution,[status(thm)],[c_55,c_1174])).

tff(c_1329,plain,(
    ! [A_107] :
      ( v2_compts_1(u1_struct_0(k1_pre_topc('#skF_1','#skF_3')),A_107)
      | ~ v2_compts_1('#skF_3',k1_pre_topc('#skF_1','#skF_3'))
      | ~ m1_subset_1(u1_struct_0(k1_pre_topc('#skF_1','#skF_3')),k1_zfmisc_1(u1_struct_0(A_107)))
      | ~ m1_pre_topc(k1_pre_topc('#skF_1','#skF_3'),A_107)
      | ~ l1_pre_topc(A_107) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_146,c_1313])).

tff(c_1333,plain,(
    ! [A_107] :
      ( v2_compts_1('#skF_3',A_107)
      | ~ v2_compts_1('#skF_3',k1_pre_topc('#skF_1','#skF_3'))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_107)))
      | ~ m1_pre_topc(k1_pre_topc('#skF_1','#skF_3'),A_107)
      | ~ l1_pre_topc(A_107) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_146,c_1329])).

tff(c_9686,plain,(
    ! [A_252] :
      ( v2_compts_1('#skF_3',A_252)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_252)))
      | ~ m1_pre_topc(k1_pre_topc('#skF_1','#skF_3'),A_252)
      | ~ l1_pre_topc(A_252) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3201,c_1333])).

tff(c_9717,plain,(
    ! [A_73] :
      ( v2_compts_1('#skF_3',A_73)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3'))
      | ~ m1_pre_topc(k1_pre_topc('#skF_1','#skF_3'),A_73)
      | ~ l1_pre_topc(A_73) ) ),
    inference(resolution,[status(thm)],[c_567,c_9686])).

tff(c_9808,plain,(
    ! [A_253] :
      ( v2_compts_1('#skF_3',A_253)
      | ~ m1_pre_topc(k1_pre_topc('#skF_1','#skF_3'),A_253)
      | ~ l1_pre_topc(A_253) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_9717])).

tff(c_9820,plain,(
    ! [B_26] :
      ( v2_compts_1('#skF_3',g1_pre_topc(u1_struct_0(B_26),u1_pre_topc(B_26)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(B_26),u1_pre_topc(B_26)))
      | ~ m1_pre_topc(k1_pre_topc('#skF_1','#skF_3'),B_26)
      | ~ l1_pre_topc(B_26)
      | ~ l1_pre_topc(k1_pre_topc('#skF_1','#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_26,c_9808])).

tff(c_58727,plain,(
    ! [B_698] :
      ( v2_compts_1('#skF_3',g1_pre_topc(u1_struct_0(B_698),u1_pre_topc(B_698)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(B_698),u1_pre_topc(B_698)))
      | ~ m1_pre_topc(k1_pre_topc('#skF_1','#skF_3'),B_698)
      | ~ l1_pre_topc(B_698) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_9820])).

tff(c_58732,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ m1_pre_topc(k1_pre_topc('#skF_1','#skF_3'),'#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_58727,c_423])).

tff(c_58853,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_114,c_1353,c_58732])).

tff(c_58855,plain,(
    v2_compts_1('#skF_3',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_38,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ v2_compts_1('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))
    | ~ v2_compts_1('#skF_3',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_58925,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ v2_compts_1('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58855,c_38])).

tff(c_58926,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))) ),
    inference(splitLeft,[status(thm)],[c_58925])).

tff(c_59054,plain,
    ( ~ m1_pre_topc('#skF_1',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_59021,c_58926])).

tff(c_59381,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_59054])).

tff(c_59384,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_90,c_59381])).

tff(c_59388,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_59384])).

tff(c_59390,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_59054])).

tff(c_59192,plain,(
    ! [B_709,A_710] :
      ( m1_subset_1(u1_struct_0(B_709),k1_zfmisc_1(u1_struct_0(A_710)))
      | ~ m1_pre_topc(B_709,A_710)
      | ~ l1_pre_topc(A_710) ) ),
    inference(resolution,[status(thm)],[c_55,c_59001])).

tff(c_59571,plain,(
    ! [A_725] :
      ( m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_725)))
      | ~ m1_pre_topc(k1_pre_topc('#skF_1','#skF_3'),A_725)
      | ~ l1_pre_topc(A_725) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_146,c_59192])).

tff(c_59578,plain,
    ( ~ m1_pre_topc(k1_pre_topc('#skF_1','#skF_3'),g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_59571,c_58926])).

tff(c_59615,plain,(
    ~ m1_pre_topc(k1_pre_topc('#skF_1','#skF_3'),g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_59390,c_59578])).

tff(c_59630,plain,
    ( ~ m1_pre_topc(k1_pre_topc('#skF_1','#skF_3'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ l1_pre_topc(k1_pre_topc('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_26,c_59615])).

tff(c_59634,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_32,c_114,c_59630])).

tff(c_59635,plain,
    ( ~ v2_compts_1('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_58925])).

tff(c_59656,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_59635])).

tff(c_59636,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))) ),
    inference(splitRight,[status(thm)],[c_58925])).

tff(c_40,plain,
    ( m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))
    | ~ v2_compts_1('#skF_3',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_59638,plain,
    ( m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58855,c_40])).

tff(c_59639,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))) ),
    inference(splitLeft,[status(thm)],[c_59638])).

tff(c_59653,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_59636,c_59639])).

tff(c_59655,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))) ),
    inference(splitRight,[status(thm)],[c_59638])).

tff(c_12,plain,(
    ! [A_5,B_6] :
      ( v1_pre_topc(k1_pre_topc(A_5,B_6))
      | ~ m1_subset_1(B_6,k1_zfmisc_1(u1_struct_0(A_5)))
      | ~ l1_pre_topc(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_59667,plain,
    ( v1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_3'))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_59655,c_12])).

tff(c_60545,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_59667])).

tff(c_60548,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_90,c_60545])).

tff(c_60552,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_60548])).

tff(c_60554,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_59667])).

tff(c_59654,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))) ),
    inference(splitRight,[status(thm)],[c_59638])).

tff(c_59678,plain,
    ( m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'),g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_59654,c_10])).

tff(c_62266,plain,(
    m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'),g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60554,c_59678])).

tff(c_22,plain,(
    ! [B_23,A_21] :
      ( m1_pre_topc(B_23,A_21)
      | ~ m1_pre_topc(B_23,g1_pre_topc(u1_struct_0(A_21),u1_pre_topc(A_21)))
      | ~ l1_pre_topc(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_62271,plain,
    ( m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_62266,c_22])).

tff(c_62280,plain,(
    m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_62271])).

tff(c_18,plain,(
    ! [A_11,B_13] :
      ( u1_struct_0(k1_pre_topc(A_11,B_13)) = B_13
      | ~ m1_subset_1(B_13,k1_zfmisc_1(u1_struct_0(A_11)))
      | ~ l1_pre_topc(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_59677,plain,
    ( u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')) = '#skF_2'
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_59654,c_18])).

tff(c_61116,plain,(
    u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60554,c_59677])).

tff(c_59756,plain,(
    ! [C_727,A_728,B_729] :
      ( m1_subset_1(C_727,k1_zfmisc_1(u1_struct_0(A_728)))
      | ~ m1_subset_1(C_727,k1_zfmisc_1(u1_struct_0(B_729)))
      | ~ m1_pre_topc(B_729,A_728)
      | ~ l1_pre_topc(A_728) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_59781,plain,(
    ! [B_729,A_728] :
      ( m1_subset_1(u1_struct_0(B_729),k1_zfmisc_1(u1_struct_0(A_728)))
      | ~ m1_pre_topc(B_729,A_728)
      | ~ l1_pre_topc(A_728) ) ),
    inference(resolution,[status(thm)],[c_55,c_59756])).

tff(c_64856,plain,(
    ! [A_833] :
      ( m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(A_833)))
      | ~ m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'),A_833)
      | ~ l1_pre_topc(A_833) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_61116,c_59781])).

tff(c_64859,plain,
    ( m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_62280,c_64856])).

tff(c_64873,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_64859])).

tff(c_64875,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_59656,c_64873])).

tff(c_64876,plain,(
    ~ v2_compts_1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_59635])).

tff(c_64877,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_59635])).

tff(c_64882,plain,
    ( m1_pre_topc(k1_pre_topc('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_64877,c_10])).

tff(c_64891,plain,(
    m1_pre_topc(k1_pre_topc('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_64882])).

tff(c_64908,plain,
    ( l1_pre_topc(k1_pre_topc('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_64891,c_14])).

tff(c_64911,plain,(
    l1_pre_topc(k1_pre_topc('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_64908])).

tff(c_64880,plain,
    ( u1_struct_0(k1_pre_topc('#skF_1','#skF_2')) = '#skF_2'
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_64877,c_18])).

tff(c_64888,plain,(
    u1_struct_0(k1_pre_topc('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_64880])).

tff(c_101,plain,(
    ! [A_59,B_60] :
      ( m1_pre_topc(k1_pre_topc(A_59,B_60),A_59)
      | ~ m1_subset_1(B_60,k1_zfmisc_1(u1_struct_0(A_59)))
      | ~ l1_pre_topc(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_105,plain,(
    ! [A_59] :
      ( m1_pre_topc(k1_pre_topc(A_59,u1_struct_0(A_59)),A_59)
      | ~ l1_pre_topc(A_59) ) ),
    inference(resolution,[status(thm)],[c_55,c_101])).

tff(c_64932,plain,
    ( m1_pre_topc(k1_pre_topc(k1_pre_topc('#skF_1','#skF_2'),'#skF_2'),k1_pre_topc('#skF_1','#skF_2'))
    | ~ l1_pre_topc(k1_pre_topc('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_64888,c_105])).

tff(c_64963,plain,(
    m1_pre_topc(k1_pre_topc(k1_pre_topc('#skF_1','#skF_2'),'#skF_2'),k1_pre_topc('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64911,c_64932])).

tff(c_147,plain,(
    ! [A_65] :
      ( u1_struct_0(k1_pre_topc(A_65,u1_struct_0(A_65))) = u1_struct_0(A_65)
      | ~ l1_pre_topc(A_65) ) ),
    inference(resolution,[status(thm)],[c_55,c_136])).

tff(c_64920,plain,
    ( u1_struct_0(k1_pre_topc(k1_pre_topc('#skF_1','#skF_2'),'#skF_2')) = u1_struct_0(k1_pre_topc('#skF_1','#skF_2'))
    | ~ l1_pre_topc(k1_pre_topc('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_64888,c_147])).

tff(c_64955,plain,(
    u1_struct_0(k1_pre_topc(k1_pre_topc('#skF_1','#skF_2'),'#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64911,c_64888,c_64920])).

tff(c_65373,plain,(
    ! [D_842,B_843,A_844] :
      ( v2_compts_1(D_842,B_843)
      | ~ v2_compts_1(D_842,A_844)
      | ~ m1_subset_1(D_842,k1_zfmisc_1(u1_struct_0(B_843)))
      | ~ m1_subset_1(D_842,k1_zfmisc_1(u1_struct_0(A_844)))
      | ~ m1_pre_topc(B_843,A_844)
      | ~ l1_pre_topc(A_844) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_67666,plain,(
    ! [B_902,A_903] :
      ( v2_compts_1(u1_struct_0(B_902),B_902)
      | ~ v2_compts_1(u1_struct_0(B_902),A_903)
      | ~ m1_subset_1(u1_struct_0(B_902),k1_zfmisc_1(u1_struct_0(A_903)))
      | ~ m1_pre_topc(B_902,A_903)
      | ~ l1_pre_topc(A_903) ) ),
    inference(resolution,[status(thm)],[c_55,c_65373])).

tff(c_67716,plain,(
    ! [B_902] :
      ( v2_compts_1(u1_struct_0(B_902),B_902)
      | ~ v2_compts_1(u1_struct_0(B_902),k1_pre_topc('#skF_1','#skF_2'))
      | ~ m1_subset_1(u1_struct_0(B_902),k1_zfmisc_1('#skF_2'))
      | ~ m1_pre_topc(B_902,k1_pre_topc('#skF_1','#skF_2'))
      | ~ l1_pre_topc(k1_pre_topc('#skF_1','#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64888,c_67666])).

tff(c_78622,plain,(
    ! [B_1020] :
      ( v2_compts_1(u1_struct_0(B_1020),B_1020)
      | ~ v2_compts_1(u1_struct_0(B_1020),k1_pre_topc('#skF_1','#skF_2'))
      | ~ m1_subset_1(u1_struct_0(B_1020),k1_zfmisc_1('#skF_2'))
      | ~ m1_pre_topc(B_1020,k1_pre_topc('#skF_1','#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64911,c_67716])).

tff(c_78674,plain,
    ( v2_compts_1(u1_struct_0(k1_pre_topc(k1_pre_topc('#skF_1','#skF_2'),'#skF_2')),k1_pre_topc(k1_pre_topc('#skF_1','#skF_2'),'#skF_2'))
    | ~ v2_compts_1('#skF_2',k1_pre_topc('#skF_1','#skF_2'))
    | ~ m1_subset_1(u1_struct_0(k1_pre_topc(k1_pre_topc('#skF_1','#skF_2'),'#skF_2')),k1_zfmisc_1('#skF_2'))
    | ~ m1_pre_topc(k1_pre_topc(k1_pre_topc('#skF_1','#skF_2'),'#skF_2'),k1_pre_topc('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_64955,c_78622])).

tff(c_78708,plain,
    ( v2_compts_1('#skF_2',k1_pre_topc(k1_pre_topc('#skF_1','#skF_2'),'#skF_2'))
    | ~ v2_compts_1('#skF_2',k1_pre_topc('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64963,c_55,c_64955,c_64955,c_78674])).

tff(c_78714,plain,(
    ~ v2_compts_1('#skF_2',k1_pre_topc('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_78708])).

tff(c_58854,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))
    | v2_compts_1('#skF_2',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_64913,plain,(
    v2_compts_1('#skF_2',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_59636,c_58854])).

tff(c_65131,plain,(
    ! [C_834,A_835,B_836] :
      ( m1_subset_1(C_834,k1_zfmisc_1(u1_struct_0(A_835)))
      | ~ m1_subset_1(C_834,k1_zfmisc_1(u1_struct_0(B_836)))
      | ~ m1_pre_topc(B_836,A_835)
      | ~ l1_pre_topc(A_835) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_65161,plain,(
    ! [A_835] :
      ( m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(A_835)))
      | ~ m1_pre_topc('#skF_1',A_835)
      | ~ l1_pre_topc(A_835) ) ),
    inference(resolution,[status(thm)],[c_64877,c_65131])).

tff(c_65391,plain,(
    ! [A_844] :
      ( v2_compts_1('#skF_2','#skF_1')
      | ~ v2_compts_1('#skF_2',A_844)
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(A_844)))
      | ~ m1_pre_topc('#skF_1',A_844)
      | ~ l1_pre_topc(A_844) ) ),
    inference(resolution,[status(thm)],[c_64877,c_65373])).

tff(c_65936,plain,(
    ! [A_867] :
      ( ~ v2_compts_1('#skF_2',A_867)
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(A_867)))
      | ~ m1_pre_topc('#skF_1',A_867)
      | ~ l1_pre_topc(A_867) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64876,c_65391])).

tff(c_65997,plain,(
    ! [A_868] :
      ( ~ v2_compts_1('#skF_2',A_868)
      | ~ m1_pre_topc('#skF_1',A_868)
      | ~ l1_pre_topc(A_868) ) ),
    inference(resolution,[status(thm)],[c_65161,c_65936])).

tff(c_66001,plain,
    ( ~ m1_pre_topc('#skF_1',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_64913,c_65997])).

tff(c_66148,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_66001])).

tff(c_66151,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_90,c_66148])).

tff(c_66155,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_66151])).

tff(c_66157,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_66001])).

tff(c_85212,plain,(
    ! [D_1104,A_1105] :
      ( v2_compts_1(D_1104,k1_pre_topc('#skF_1','#skF_2'))
      | ~ v2_compts_1(D_1104,A_1105)
      | ~ m1_subset_1(D_1104,k1_zfmisc_1('#skF_2'))
      | ~ m1_subset_1(D_1104,k1_zfmisc_1(u1_struct_0(A_1105)))
      | ~ m1_pre_topc(k1_pre_topc('#skF_1','#skF_2'),A_1105)
      | ~ l1_pre_topc(A_1105) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64888,c_65373])).

tff(c_85356,plain,
    ( v2_compts_1('#skF_2',k1_pre_topc('#skF_1','#skF_2'))
    | ~ v2_compts_1('#skF_2',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1('#skF_2'))
    | ~ m1_pre_topc(k1_pre_topc('#skF_1','#skF_2'),g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_59654,c_85212])).

tff(c_85465,plain,
    ( v2_compts_1('#skF_2',k1_pre_topc('#skF_1','#skF_2'))
    | ~ m1_pre_topc(k1_pre_topc('#skF_1','#skF_2'),g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66157,c_55,c_64913,c_85356])).

tff(c_85466,plain,(
    ~ m1_pre_topc(k1_pre_topc('#skF_1','#skF_2'),g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_78714,c_85465])).

tff(c_85491,plain,
    ( ~ m1_pre_topc(k1_pre_topc('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ l1_pre_topc(k1_pre_topc('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_26,c_85466])).

tff(c_85495,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64911,c_32,c_64891,c_85491])).

tff(c_85497,plain,(
    v2_compts_1('#skF_2',k1_pre_topc('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_78708])).

tff(c_65559,plain,(
    ! [D_852,A_853,B_854] :
      ( v2_compts_1(D_852,A_853)
      | ~ v2_compts_1(D_852,B_854)
      | ~ m1_subset_1(D_852,k1_zfmisc_1(u1_struct_0(B_854)))
      | ~ m1_subset_1(D_852,k1_zfmisc_1(u1_struct_0(A_853)))
      | ~ m1_pre_topc(B_854,A_853)
      | ~ l1_pre_topc(A_853) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_67354,plain,(
    ! [B_895,A_896] :
      ( v2_compts_1(u1_struct_0(B_895),A_896)
      | ~ v2_compts_1(u1_struct_0(B_895),B_895)
      | ~ m1_subset_1(u1_struct_0(B_895),k1_zfmisc_1(u1_struct_0(A_896)))
      | ~ m1_pre_topc(B_895,A_896)
      | ~ l1_pre_topc(A_896) ) ),
    inference(resolution,[status(thm)],[c_55,c_65559])).

tff(c_67376,plain,(
    ! [A_896] :
      ( v2_compts_1(u1_struct_0(k1_pre_topc('#skF_1','#skF_2')),A_896)
      | ~ v2_compts_1('#skF_2',k1_pre_topc('#skF_1','#skF_2'))
      | ~ m1_subset_1(u1_struct_0(k1_pre_topc('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0(A_896)))
      | ~ m1_pre_topc(k1_pre_topc('#skF_1','#skF_2'),A_896)
      | ~ l1_pre_topc(A_896) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64888,c_67354])).

tff(c_67393,plain,(
    ! [A_896] :
      ( v2_compts_1('#skF_2',A_896)
      | ~ v2_compts_1('#skF_2',k1_pre_topc('#skF_1','#skF_2'))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(A_896)))
      | ~ m1_pre_topc(k1_pre_topc('#skF_1','#skF_2'),A_896)
      | ~ l1_pre_topc(A_896) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64888,c_64888,c_67376])).

tff(c_85603,plain,(
    ! [A_1108] :
      ( v2_compts_1('#skF_2',A_1108)
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(A_1108)))
      | ~ m1_pre_topc(k1_pre_topc('#skF_1','#skF_2'),A_1108)
      | ~ l1_pre_topc(A_1108) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85497,c_67393])).

tff(c_85710,plain,
    ( v2_compts_1('#skF_2','#skF_1')
    | ~ m1_pre_topc(k1_pre_topc('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_64877,c_85603])).

tff(c_85771,plain,(
    v2_compts_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_64891,c_85710])).

tff(c_85773,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64876,c_85771])).

tff(c_85775,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_44,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ v2_compts_1('#skF_2','#skF_1')
    | m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_85839,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ v2_compts_1('#skF_2','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_85775,c_44])).

tff(c_85840,plain,(
    ~ v2_compts_1('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_85839])).

tff(c_46,plain,
    ( m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))
    | m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_85853,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))) ),
    inference(negUnitSimplification,[status(thm)],[c_85775,c_46])).

tff(c_85864,plain,
    ( v1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_85853,c_12])).

tff(c_85865,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_85864])).

tff(c_85869,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_90,c_85865])).

tff(c_85873,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_85869])).

tff(c_85875,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_85864])).

tff(c_85863,plain,
    ( m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'),g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_85853,c_10])).

tff(c_86326,plain,(
    m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'),g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85875,c_85863])).

tff(c_86343,plain,
    ( m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_86326,c_22])).

tff(c_86364,plain,(
    m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_86343])).

tff(c_85862,plain,
    ( u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')) = '#skF_2'
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_85853,c_18])).

tff(c_86034,plain,(
    u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_85875,c_85862])).

tff(c_85876,plain,(
    ! [C_1118,A_1119,B_1120] :
      ( m1_subset_1(C_1118,k1_zfmisc_1(u1_struct_0(A_1119)))
      | ~ m1_subset_1(C_1118,k1_zfmisc_1(u1_struct_0(B_1120)))
      | ~ m1_pre_topc(B_1120,A_1119)
      | ~ l1_pre_topc(A_1119) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_85885,plain,(
    ! [B_1120,A_1119] :
      ( m1_subset_1(u1_struct_0(B_1120),k1_zfmisc_1(u1_struct_0(A_1119)))
      | ~ m1_pre_topc(B_1120,A_1119)
      | ~ l1_pre_topc(A_1119) ) ),
    inference(resolution,[status(thm)],[c_55,c_85876])).

tff(c_86052,plain,(
    ! [A_1119] :
      ( m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(A_1119)))
      | ~ m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'),A_1119)
      | ~ l1_pre_topc(A_1119) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_86034,c_85885])).

tff(c_86374,plain,
    ( m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_86364,c_86052])).

tff(c_86391,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_86374])).

tff(c_85774,plain,(
    v2_compts_1('#skF_2',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_85907,plain,(
    ! [D_1123,A_1124,B_1125] :
      ( v2_compts_1(D_1123,A_1124)
      | ~ v2_compts_1(D_1123,B_1125)
      | ~ m1_subset_1(D_1123,k1_zfmisc_1(u1_struct_0(B_1125)))
      | ~ m1_subset_1(D_1123,k1_zfmisc_1(u1_struct_0(A_1124)))
      | ~ m1_pre_topc(B_1125,A_1124)
      | ~ l1_pre_topc(A_1124) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_86782,plain,(
    ! [B_1159,A_1160] :
      ( v2_compts_1(u1_struct_0(B_1159),A_1160)
      | ~ v2_compts_1(u1_struct_0(B_1159),B_1159)
      | ~ m1_subset_1(u1_struct_0(B_1159),k1_zfmisc_1(u1_struct_0(A_1160)))
      | ~ m1_pre_topc(B_1159,A_1160)
      | ~ l1_pre_topc(A_1160) ) ),
    inference(resolution,[status(thm)],[c_55,c_85907])).

tff(c_86788,plain,(
    ! [A_1160] :
      ( v2_compts_1(u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')),A_1160)
      | ~ v2_compts_1('#skF_2',k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'))
      | ~ m1_subset_1(u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')),k1_zfmisc_1(u1_struct_0(A_1160)))
      | ~ m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'),A_1160)
      | ~ l1_pre_topc(A_1160) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_86034,c_86782])).

tff(c_86795,plain,(
    ! [A_1160] :
      ( v2_compts_1('#skF_2',A_1160)
      | ~ v2_compts_1('#skF_2',k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(A_1160)))
      | ~ m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'),A_1160)
      | ~ l1_pre_topc(A_1160) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86034,c_86034,c_86788])).

tff(c_95017,plain,(
    ~ v2_compts_1('#skF_2',k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_86795])).

tff(c_86144,plain,(
    ! [D_1138,B_1139,A_1140] :
      ( v2_compts_1(D_1138,B_1139)
      | ~ v2_compts_1(D_1138,A_1140)
      | ~ m1_subset_1(D_1138,k1_zfmisc_1(u1_struct_0(B_1139)))
      | ~ m1_subset_1(D_1138,k1_zfmisc_1(u1_struct_0(A_1140)))
      | ~ m1_pre_topc(B_1139,A_1140)
      | ~ l1_pre_topc(A_1140) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_86840,plain,(
    ! [B_1162,A_1163] :
      ( v2_compts_1(u1_struct_0(B_1162),B_1162)
      | ~ v2_compts_1(u1_struct_0(B_1162),A_1163)
      | ~ m1_subset_1(u1_struct_0(B_1162),k1_zfmisc_1(u1_struct_0(A_1163)))
      | ~ m1_pre_topc(B_1162,A_1163)
      | ~ l1_pre_topc(A_1163) ) ),
    inference(resolution,[status(thm)],[c_55,c_86144])).

tff(c_86850,plain,(
    ! [A_1163] :
      ( v2_compts_1(u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')),k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'))
      | ~ v2_compts_1(u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')),A_1163)
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(A_1163)))
      | ~ m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'),A_1163)
      | ~ l1_pre_topc(A_1163) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_86034,c_86840])).

tff(c_86872,plain,(
    ! [A_1163] :
      ( v2_compts_1('#skF_2',k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'))
      | ~ v2_compts_1('#skF_2',A_1163)
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(A_1163)))
      | ~ m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'),A_1163)
      | ~ l1_pre_topc(A_1163) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86034,c_86034,c_86850])).

tff(c_95386,plain,(
    ! [A_1271] :
      ( ~ v2_compts_1('#skF_2',A_1271)
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(A_1271)))
      | ~ m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'),A_1271)
      | ~ l1_pre_topc(A_1271) ) ),
    inference(negUnitSimplification,[status(thm)],[c_95017,c_86872])).

tff(c_95408,plain,
    ( ~ v2_compts_1('#skF_2',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_86326,c_95386])).

tff(c_95431,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_85875,c_85853,c_85774,c_95408])).

tff(c_95807,plain,(
    ! [A_1278] :
      ( v2_compts_1('#skF_2',A_1278)
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(A_1278)))
      | ~ m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'),A_1278)
      | ~ l1_pre_topc(A_1278) ) ),
    inference(splitRight,[status(thm)],[c_86795])).

tff(c_95826,plain,
    ( v2_compts_1('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_86364,c_95807])).

tff(c_95848,plain,(
    v2_compts_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_86391,c_95826])).

tff(c_95850,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_85840,c_95848])).

tff(c_95851,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_85839])).

tff(c_95853,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))) ),
    inference(negUnitSimplification,[status(thm)],[c_85775,c_46])).

tff(c_95864,plain,
    ( v1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_95853,c_12])).

tff(c_95878,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_95864])).

tff(c_95881,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_90,c_95878])).

tff(c_95885,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_95881])).

tff(c_95887,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_95864])).

tff(c_95863,plain,
    ( m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'),g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_95853,c_10])).

tff(c_96333,plain,(
    m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'),g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_95887,c_95863])).

tff(c_96347,plain,
    ( m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_96333,c_22])).

tff(c_96365,plain,(
    m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_96347])).

tff(c_95862,plain,
    ( u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')) = '#skF_2'
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_95853,c_18])).

tff(c_96030,plain,(
    u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_95887,c_95862])).

tff(c_95888,plain,(
    ! [C_1281,A_1282,B_1283] :
      ( m1_subset_1(C_1281,k1_zfmisc_1(u1_struct_0(A_1282)))
      | ~ m1_subset_1(C_1281,k1_zfmisc_1(u1_struct_0(B_1283)))
      | ~ m1_pre_topc(B_1283,A_1282)
      | ~ l1_pre_topc(A_1282) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_95897,plain,(
    ! [B_1283,A_1282] :
      ( m1_subset_1(u1_struct_0(B_1283),k1_zfmisc_1(u1_struct_0(A_1282)))
      | ~ m1_pre_topc(B_1283,A_1282)
      | ~ l1_pre_topc(A_1282) ) ),
    inference(resolution,[status(thm)],[c_55,c_95888])).

tff(c_96046,plain,(
    ! [A_1282] :
      ( m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(A_1282)))
      | ~ m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'),A_1282)
      | ~ l1_pre_topc(A_1282) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_96030,c_95897])).

tff(c_96372,plain,
    ( m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_96365,c_96046])).

tff(c_96386,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_96372])).

tff(c_96388,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_95851,c_96386])).

tff(c_96390,plain,(
    ~ v2_compts_1('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_50,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ v2_compts_1('#skF_2','#skF_1')
    | v2_compts_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_96403,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ v2_compts_1('#skF_2','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_96390,c_50])).

tff(c_96404,plain,(
    ~ v2_compts_1('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_96403])).

tff(c_96392,plain,(
    ! [A_1320] :
      ( m1_subset_1(u1_pre_topc(A_1320),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_1320))))
      | ~ l1_pre_topc(A_1320) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_96400,plain,(
    ! [A_1320] :
      ( l1_pre_topc(g1_pre_topc(u1_struct_0(A_1320),u1_pre_topc(A_1320)))
      | ~ l1_pre_topc(A_1320) ) ),
    inference(resolution,[status(thm)],[c_96392,c_6])).

tff(c_52,plain,
    ( m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))
    | v2_compts_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_96414,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))) ),
    inference(negUnitSimplification,[status(thm)],[c_96390,c_52])).

tff(c_96418,plain,
    ( v1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_96414,c_12])).

tff(c_96505,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_96418])).

tff(c_96518,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_96400,c_96505])).

tff(c_96522,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_96518])).

tff(c_96524,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_96418])).

tff(c_96419,plain,(
    ! [A_1328,B_1329] :
      ( m1_pre_topc(k1_pre_topc(A_1328,B_1329),A_1328)
      | ~ m1_subset_1(B_1329,k1_zfmisc_1(u1_struct_0(A_1328)))
      | ~ l1_pre_topc(A_1328) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_96425,plain,
    ( m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'),g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_96414,c_96419])).

tff(c_97091,plain,(
    m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'),g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96524,c_96425])).

tff(c_97110,plain,
    ( m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_97091,c_22])).

tff(c_97134,plain,(
    m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_97110])).

tff(c_96438,plain,(
    ! [A_1332,B_1333] :
      ( u1_struct_0(k1_pre_topc(A_1332,B_1333)) = B_1333
      | ~ m1_subset_1(B_1333,k1_zfmisc_1(u1_struct_0(A_1332)))
      | ~ l1_pre_topc(A_1332) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_96446,plain,
    ( u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')) = '#skF_2'
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_96414,c_96438])).

tff(c_96683,plain,(
    u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_96524,c_96446])).

tff(c_96526,plain,(
    ! [C_1340,A_1341,B_1342] :
      ( m1_subset_1(C_1340,k1_zfmisc_1(u1_struct_0(A_1341)))
      | ~ m1_subset_1(C_1340,k1_zfmisc_1(u1_struct_0(B_1342)))
      | ~ m1_pre_topc(B_1342,A_1341)
      | ~ l1_pre_topc(A_1341) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_96535,plain,(
    ! [B_1342,A_1341] :
      ( m1_subset_1(u1_struct_0(B_1342),k1_zfmisc_1(u1_struct_0(A_1341)))
      | ~ m1_pre_topc(B_1342,A_1341)
      | ~ l1_pre_topc(A_1341) ) ),
    inference(resolution,[status(thm)],[c_55,c_96526])).

tff(c_96701,plain,(
    ! [A_1341] :
      ( m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(A_1341)))
      | ~ m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'),A_1341)
      | ~ l1_pre_topc(A_1341) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_96683,c_96535])).

tff(c_97147,plain,
    ( m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_97134,c_96701])).

tff(c_97168,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_97147])).

tff(c_96389,plain,(
    v2_compts_1('#skF_2',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_96578,plain,(
    ! [D_1351,A_1352,B_1353] :
      ( v2_compts_1(D_1351,A_1352)
      | ~ v2_compts_1(D_1351,B_1353)
      | ~ m1_subset_1(D_1351,k1_zfmisc_1(u1_struct_0(B_1353)))
      | ~ m1_subset_1(D_1351,k1_zfmisc_1(u1_struct_0(A_1352)))
      | ~ m1_pre_topc(B_1353,A_1352)
      | ~ l1_pre_topc(A_1352) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_97640,plain,(
    ! [B_1387,A_1388] :
      ( v2_compts_1(u1_struct_0(B_1387),A_1388)
      | ~ v2_compts_1(u1_struct_0(B_1387),B_1387)
      | ~ m1_subset_1(u1_struct_0(B_1387),k1_zfmisc_1(u1_struct_0(A_1388)))
      | ~ m1_pre_topc(B_1387,A_1388)
      | ~ l1_pre_topc(A_1388) ) ),
    inference(resolution,[status(thm)],[c_55,c_96578])).

tff(c_97646,plain,(
    ! [A_1388] :
      ( v2_compts_1(u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')),A_1388)
      | ~ v2_compts_1('#skF_2',k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'))
      | ~ m1_subset_1(u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')),k1_zfmisc_1(u1_struct_0(A_1388)))
      | ~ m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'),A_1388)
      | ~ l1_pre_topc(A_1388) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_96683,c_97640])).

tff(c_97653,plain,(
    ! [A_1388] :
      ( v2_compts_1('#skF_2',A_1388)
      | ~ v2_compts_1('#skF_2',k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(A_1388)))
      | ~ m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'),A_1388)
      | ~ l1_pre_topc(A_1388) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96683,c_96683,c_97646])).

tff(c_104798,plain,(
    ~ v2_compts_1('#skF_2',k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_97653])).

tff(c_96826,plain,(
    ! [D_1363,B_1364,A_1365] :
      ( v2_compts_1(D_1363,B_1364)
      | ~ v2_compts_1(D_1363,A_1365)
      | ~ m1_subset_1(D_1363,k1_zfmisc_1(u1_struct_0(B_1364)))
      | ~ m1_subset_1(D_1363,k1_zfmisc_1(u1_struct_0(A_1365)))
      | ~ m1_pre_topc(B_1364,A_1365)
      | ~ l1_pre_topc(A_1365) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_97387,plain,(
    ! [B_1384,A_1385] :
      ( v2_compts_1(u1_struct_0(B_1384),B_1384)
      | ~ v2_compts_1(u1_struct_0(B_1384),A_1385)
      | ~ m1_subset_1(u1_struct_0(B_1384),k1_zfmisc_1(u1_struct_0(A_1385)))
      | ~ m1_pre_topc(B_1384,A_1385)
      | ~ l1_pre_topc(A_1385) ) ),
    inference(resolution,[status(thm)],[c_55,c_96826])).

tff(c_97393,plain,(
    ! [A_1385] :
      ( v2_compts_1(u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')),k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'))
      | ~ v2_compts_1(u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')),A_1385)
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(A_1385)))
      | ~ m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'),A_1385)
      | ~ l1_pre_topc(A_1385) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_96683,c_97387])).

tff(c_97412,plain,(
    ! [A_1385] :
      ( v2_compts_1('#skF_2',k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'))
      | ~ v2_compts_1('#skF_2',A_1385)
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(A_1385)))
      | ~ m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'),A_1385)
      | ~ l1_pre_topc(A_1385) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96683,c_96683,c_97393])).

tff(c_105150,plain,(
    ! [A_1485] :
      ( ~ v2_compts_1('#skF_2',A_1485)
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(A_1485)))
      | ~ m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'),A_1485)
      | ~ l1_pre_topc(A_1485) ) ),
    inference(negUnitSimplification,[status(thm)],[c_104798,c_97412])).

tff(c_105172,plain,
    ( ~ v2_compts_1('#skF_2',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_97091,c_105150])).

tff(c_105195,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_96524,c_96414,c_96389,c_105172])).

tff(c_105554,plain,(
    ! [A_1486] :
      ( v2_compts_1('#skF_2',A_1486)
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(A_1486)))
      | ~ m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'),A_1486)
      | ~ l1_pre_topc(A_1486) ) ),
    inference(splitRight,[status(thm)],[c_97653])).

tff(c_105573,plain,
    ( v2_compts_1('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_97134,c_105554])).

tff(c_105595,plain,(
    v2_compts_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_97168,c_105573])).

tff(c_105597,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_96404,c_105595])).

tff(c_105598,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_96403])).

tff(c_105675,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))) ),
    inference(negUnitSimplification,[status(thm)],[c_96390,c_52])).

tff(c_105686,plain,
    ( v1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_105675,c_12])).

tff(c_105702,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_105686])).

tff(c_105705,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_96400,c_105702])).

tff(c_105709,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_105705])).

tff(c_105711,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_105686])).

tff(c_105684,plain,
    ( m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'),g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_105675,c_10])).

tff(c_106382,plain,(
    m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'),g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_105711,c_105684])).

tff(c_106401,plain,
    ( m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_106382,c_22])).

tff(c_106425,plain,(
    m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_106401])).

tff(c_105685,plain,
    ( u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')) = '#skF_2'
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_105675,c_18])).

tff(c_105853,plain,(
    u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_105711,c_105685])).

tff(c_105712,plain,(
    ! [C_1501,A_1502,B_1503] :
      ( m1_subset_1(C_1501,k1_zfmisc_1(u1_struct_0(A_1502)))
      | ~ m1_subset_1(C_1501,k1_zfmisc_1(u1_struct_0(B_1503)))
      | ~ m1_pre_topc(B_1503,A_1502)
      | ~ l1_pre_topc(A_1502) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_105721,plain,(
    ! [B_1503,A_1502] :
      ( m1_subset_1(u1_struct_0(B_1503),k1_zfmisc_1(u1_struct_0(A_1502)))
      | ~ m1_pre_topc(B_1503,A_1502)
      | ~ l1_pre_topc(A_1502) ) ),
    inference(resolution,[status(thm)],[c_55,c_105712])).

tff(c_105869,plain,(
    ! [A_1502] :
      ( m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(A_1502)))
      | ~ m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'),A_1502)
      | ~ l1_pre_topc(A_1502) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_105853,c_105721])).

tff(c_106440,plain,
    ( m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_106425,c_105869])).

tff(c_106461,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_106440])).

tff(c_106463,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_105598,c_106461])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:24:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 33.61/22.00  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 33.61/22.04  
% 33.61/22.04  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 33.61/22.05  %$ v2_compts_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > l1_pre_topc > k1_pre_topc > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_subset_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 33.61/22.05  
% 33.61/22.05  %Foreground sorts:
% 33.61/22.05  
% 33.61/22.05  
% 33.61/22.05  %Background operators:
% 33.61/22.05  
% 33.61/22.05  
% 33.61/22.05  %Foreground operators:
% 33.61/22.05  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 33.61/22.05  tff(k1_pre_topc, type, k1_pre_topc: ($i * $i) > $i).
% 33.61/22.05  tff(v2_compts_1, type, v2_compts_1: ($i * $i) > $o).
% 33.61/22.05  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 33.61/22.05  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 33.61/22.05  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 33.61/22.05  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 33.61/22.05  tff('#skF_2', type, '#skF_2': $i).
% 33.61/22.05  tff('#skF_3', type, '#skF_3': $i).
% 33.61/22.05  tff('#skF_1', type, '#skF_1': $i).
% 33.61/22.05  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 33.61/22.05  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 33.61/22.05  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 33.61/22.05  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 33.61/22.05  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 33.61/22.05  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 33.61/22.05  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 33.61/22.05  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 33.61/22.05  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 33.61/22.05  
% 33.97/22.08  tff(f_121, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v2_compts_1(B, A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) <=> (v2_compts_1(B, g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_compts_1)).
% 33.97/22.08  tff(f_43, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v1_pre_topc(k1_pre_topc(A, B)) & m1_pre_topc(k1_pre_topc(A, B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_pre_topc)).
% 33.97/22.08  tff(f_50, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 33.97/22.08  tff(f_87, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (m1_pre_topc(A, B) <=> m1_pre_topc(A, g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_pre_topc)).
% 33.97/22.08  tff(f_54, axiom, (![A]: (l1_pre_topc(A) => m1_subset_1(u1_pre_topc(A), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 33.97/22.08  tff(f_35, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (v1_pre_topc(g1_pre_topc(A, B)) & l1_pre_topc(g1_pre_topc(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_g1_pre_topc)).
% 33.97/22.08  tff(f_71, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B))) => m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_pre_topc)).
% 33.97/22.08  tff(f_104, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => ((C = D) => (v2_compts_1(C, A) <=> v2_compts_1(D, B))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_compts_1)).
% 33.97/22.08  tff(f_27, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 33.97/22.08  tff(f_29, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 33.97/22.08  tff(f_61, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (u1_struct_0(k1_pre_topc(A, B)) = B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_pre_topc)).
% 33.97/22.08  tff(f_78, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) => m1_pre_topc(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_pre_topc)).
% 33.97/22.08  tff(c_32, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_121])).
% 33.97/22.08  tff(c_48, plain, (v2_compts_1('#skF_2', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_121])).
% 33.97/22.08  tff(c_106, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_48])).
% 33.97/22.08  tff(c_10, plain, (![A_5, B_6]: (m1_pre_topc(k1_pre_topc(A_5, B_6), A_5) | ~m1_subset_1(B_6, k1_zfmisc_1(u1_struct_0(A_5))) | ~l1_pre_topc(A_5))), inference(cnfTransformation, [status(thm)], [f_43])).
% 33.97/22.08  tff(c_108, plain, (m1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'), '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_106, c_10])).
% 33.97/22.08  tff(c_114, plain, (m1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_108])).
% 33.97/22.08  tff(c_14, plain, (![B_9, A_7]: (l1_pre_topc(B_9) | ~m1_pre_topc(B_9, A_7) | ~l1_pre_topc(A_7))), inference(cnfTransformation, [status(thm)], [f_50])).
% 33.97/22.08  tff(c_120, plain, (l1_pre_topc(k1_pre_topc('#skF_1', '#skF_3')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_114, c_14])).
% 33.97/22.08  tff(c_123, plain, (l1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_120])).
% 33.97/22.08  tff(c_26, plain, (![A_24, B_26]: (m1_pre_topc(A_24, g1_pre_topc(u1_struct_0(B_26), u1_pre_topc(B_26))) | ~m1_pre_topc(A_24, B_26) | ~l1_pre_topc(B_26) | ~l1_pre_topc(A_24))), inference(cnfTransformation, [status(thm)], [f_87])).
% 33.97/22.08  tff(c_82, plain, (![A_53]: (m1_subset_1(u1_pre_topc(A_53), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_53)))) | ~l1_pre_topc(A_53))), inference(cnfTransformation, [status(thm)], [f_54])).
% 33.97/22.08  tff(c_6, plain, (![A_3, B_4]: (l1_pre_topc(g1_pre_topc(A_3, B_4)) | ~m1_subset_1(B_4, k1_zfmisc_1(k1_zfmisc_1(A_3))))), inference(cnfTransformation, [status(thm)], [f_35])).
% 33.97/22.08  tff(c_90, plain, (![A_53]: (l1_pre_topc(g1_pre_topc(u1_struct_0(A_53), u1_pre_topc(A_53))) | ~l1_pre_topc(A_53))), inference(resolution, [status(thm)], [c_82, c_6])).
% 33.97/22.08  tff(c_59001, plain, (![C_701, A_702, B_703]: (m1_subset_1(C_701, k1_zfmisc_1(u1_struct_0(A_702))) | ~m1_subset_1(C_701, k1_zfmisc_1(u1_struct_0(B_703))) | ~m1_pre_topc(B_703, A_702) | ~l1_pre_topc(A_702))), inference(cnfTransformation, [status(thm)], [f_71])).
% 33.97/22.08  tff(c_59021, plain, (![A_704]: (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_704))) | ~m1_pre_topc('#skF_1', A_704) | ~l1_pre_topc(A_704))), inference(resolution, [status(thm)], [c_106, c_59001])).
% 33.97/22.08  tff(c_555, plain, (![C_72, A_73, B_74]: (m1_subset_1(C_72, k1_zfmisc_1(u1_struct_0(A_73))) | ~m1_subset_1(C_72, k1_zfmisc_1(u1_struct_0(B_74))) | ~m1_pre_topc(B_74, A_73) | ~l1_pre_topc(A_73))), inference(cnfTransformation, [status(thm)], [f_71])).
% 33.97/22.08  tff(c_573, plain, (![A_73]: (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_73))) | ~m1_pre_topc('#skF_1', A_73) | ~l1_pre_topc(A_73))), inference(resolution, [status(thm)], [c_106, c_555])).
% 33.97/22.08  tff(c_54, plain, (v2_compts_1('#skF_2', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | v2_compts_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_121])).
% 33.97/22.08  tff(c_80, plain, (v2_compts_1('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_54])).
% 33.97/22.08  tff(c_1174, plain, (![D_98, A_99, B_100]: (v2_compts_1(D_98, A_99) | ~v2_compts_1(D_98, B_100) | ~m1_subset_1(D_98, k1_zfmisc_1(u1_struct_0(B_100))) | ~m1_subset_1(D_98, k1_zfmisc_1(u1_struct_0(A_99))) | ~m1_pre_topc(B_100, A_99) | ~l1_pre_topc(A_99))), inference(cnfTransformation, [status(thm)], [f_104])).
% 33.97/22.08  tff(c_1198, plain, (![A_99]: (v2_compts_1('#skF_3', A_99) | ~v2_compts_1('#skF_3', '#skF_1') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_99))) | ~m1_pre_topc('#skF_1', A_99) | ~l1_pre_topc(A_99))), inference(resolution, [status(thm)], [c_106, c_1174])).
% 33.97/22.08  tff(c_1228, plain, (![A_103]: (v2_compts_1('#skF_3', A_103) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_103))) | ~m1_pre_topc('#skF_1', A_103) | ~l1_pre_topc(A_103))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_1198])).
% 33.97/22.08  tff(c_1277, plain, (![A_104]: (v2_compts_1('#skF_3', A_104) | ~m1_pre_topc('#skF_1', A_104) | ~l1_pre_topc(A_104))), inference(resolution, [status(thm)], [c_573, c_1228])).
% 33.97/22.08  tff(c_42, plain, (v2_compts_1('#skF_2', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))) | ~v2_compts_1('#skF_3', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_121])).
% 33.97/22.08  tff(c_423, plain, (~v2_compts_1('#skF_3', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitLeft, [status(thm)], [c_42])).
% 33.97/22.08  tff(c_1281, plain, (~m1_pre_topc('#skF_1', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(resolution, [status(thm)], [c_1277, c_423])).
% 33.97/22.08  tff(c_1344, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitLeft, [status(thm)], [c_1281])).
% 33.97/22.08  tff(c_1347, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_90, c_1344])).
% 33.97/22.08  tff(c_1351, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_1347])).
% 33.97/22.08  tff(c_1353, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitRight, [status(thm)], [c_1281])).
% 33.97/22.08  tff(c_2, plain, (![A_1]: (k2_subset_1(A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 33.97/22.08  tff(c_4, plain, (![A_2]: (m1_subset_1(k2_subset_1(A_2), k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 33.97/22.08  tff(c_55, plain, (![A_2]: (m1_subset_1(A_2, k1_zfmisc_1(A_2)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_4])).
% 33.97/22.08  tff(c_136, plain, (![A_65, B_66]: (u1_struct_0(k1_pre_topc(A_65, B_66))=B_66 | ~m1_subset_1(B_66, k1_zfmisc_1(u1_struct_0(A_65))) | ~l1_pre_topc(A_65))), inference(cnfTransformation, [status(thm)], [f_61])).
% 33.97/22.08  tff(c_139, plain, (u1_struct_0(k1_pre_topc('#skF_1', '#skF_3'))='#skF_3' | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_106, c_136])).
% 33.97/22.08  tff(c_146, plain, (u1_struct_0(k1_pre_topc('#skF_1', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_139])).
% 33.97/22.08  tff(c_567, plain, (![C_72, A_73]: (m1_subset_1(C_72, k1_zfmisc_1(u1_struct_0(A_73))) | ~m1_subset_1(C_72, k1_zfmisc_1('#skF_3')) | ~m1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'), A_73) | ~l1_pre_topc(A_73))), inference(superposition, [status(thm), theory('equality')], [c_146, c_555])).
% 33.97/22.08  tff(c_574, plain, (![B_74, A_73]: (m1_subset_1(u1_struct_0(B_74), k1_zfmisc_1(u1_struct_0(A_73))) | ~m1_pre_topc(B_74, A_73) | ~l1_pre_topc(A_73))), inference(resolution, [status(thm)], [c_55, c_555])).
% 33.97/22.08  tff(c_855, plain, (![D_85, B_86, A_87]: (v2_compts_1(D_85, B_86) | ~v2_compts_1(D_85, A_87) | ~m1_subset_1(D_85, k1_zfmisc_1(u1_struct_0(B_86))) | ~m1_subset_1(D_85, k1_zfmisc_1(u1_struct_0(A_87))) | ~m1_pre_topc(B_86, A_87) | ~l1_pre_topc(A_87))), inference(cnfTransformation, [status(thm)], [f_104])).
% 33.97/22.08  tff(c_1367, plain, (![B_109, A_110]: (v2_compts_1(u1_struct_0(B_109), B_109) | ~v2_compts_1(u1_struct_0(B_109), A_110) | ~m1_subset_1(u1_struct_0(B_109), k1_zfmisc_1(u1_struct_0(A_110))) | ~m1_pre_topc(B_109, A_110) | ~l1_pre_topc(A_110))), inference(resolution, [status(thm)], [c_55, c_855])).
% 33.97/22.08  tff(c_1420, plain, (![B_112, A_113]: (v2_compts_1(u1_struct_0(B_112), B_112) | ~v2_compts_1(u1_struct_0(B_112), A_113) | ~m1_pre_topc(B_112, A_113) | ~l1_pre_topc(A_113))), inference(resolution, [status(thm)], [c_574, c_1367])).
% 33.97/22.08  tff(c_1436, plain, (![A_113]: (v2_compts_1(u1_struct_0(k1_pre_topc('#skF_1', '#skF_3')), k1_pre_topc('#skF_1', '#skF_3')) | ~v2_compts_1('#skF_3', A_113) | ~m1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'), A_113) | ~l1_pre_topc(A_113))), inference(superposition, [status(thm), theory('equality')], [c_146, c_1420])).
% 33.97/22.08  tff(c_1440, plain, (![A_113]: (v2_compts_1('#skF_3', k1_pre_topc('#skF_1', '#skF_3')) | ~v2_compts_1('#skF_3', A_113) | ~m1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'), A_113) | ~l1_pre_topc(A_113))), inference(demodulation, [status(thm), theory('equality')], [c_146, c_1436])).
% 33.97/22.08  tff(c_3172, plain, (![A_145]: (~v2_compts_1('#skF_3', A_145) | ~m1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'), A_145) | ~l1_pre_topc(A_145))), inference(splitLeft, [status(thm)], [c_1440])).
% 33.97/22.08  tff(c_3187, plain, (~v2_compts_1('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_114, c_3172])).
% 33.97/22.08  tff(c_3200, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_80, c_3187])).
% 33.97/22.08  tff(c_3201, plain, (v2_compts_1('#skF_3', k1_pre_topc('#skF_1', '#skF_3'))), inference(splitRight, [status(thm)], [c_1440])).
% 33.97/22.08  tff(c_1313, plain, (![B_106, A_107]: (v2_compts_1(u1_struct_0(B_106), A_107) | ~v2_compts_1(u1_struct_0(B_106), B_106) | ~m1_subset_1(u1_struct_0(B_106), k1_zfmisc_1(u1_struct_0(A_107))) | ~m1_pre_topc(B_106, A_107) | ~l1_pre_topc(A_107))), inference(resolution, [status(thm)], [c_55, c_1174])).
% 33.97/22.08  tff(c_1329, plain, (![A_107]: (v2_compts_1(u1_struct_0(k1_pre_topc('#skF_1', '#skF_3')), A_107) | ~v2_compts_1('#skF_3', k1_pre_topc('#skF_1', '#skF_3')) | ~m1_subset_1(u1_struct_0(k1_pre_topc('#skF_1', '#skF_3')), k1_zfmisc_1(u1_struct_0(A_107))) | ~m1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'), A_107) | ~l1_pre_topc(A_107))), inference(superposition, [status(thm), theory('equality')], [c_146, c_1313])).
% 33.97/22.08  tff(c_1333, plain, (![A_107]: (v2_compts_1('#skF_3', A_107) | ~v2_compts_1('#skF_3', k1_pre_topc('#skF_1', '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_107))) | ~m1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'), A_107) | ~l1_pre_topc(A_107))), inference(demodulation, [status(thm), theory('equality')], [c_146, c_146, c_1329])).
% 33.97/22.08  tff(c_9686, plain, (![A_252]: (v2_compts_1('#skF_3', A_252) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_252))) | ~m1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'), A_252) | ~l1_pre_topc(A_252))), inference(demodulation, [status(thm), theory('equality')], [c_3201, c_1333])).
% 33.97/22.08  tff(c_9717, plain, (![A_73]: (v2_compts_1('#skF_3', A_73) | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3')) | ~m1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'), A_73) | ~l1_pre_topc(A_73))), inference(resolution, [status(thm)], [c_567, c_9686])).
% 33.97/22.08  tff(c_9808, plain, (![A_253]: (v2_compts_1('#skF_3', A_253) | ~m1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'), A_253) | ~l1_pre_topc(A_253))), inference(demodulation, [status(thm), theory('equality')], [c_55, c_9717])).
% 33.97/22.08  tff(c_9820, plain, (![B_26]: (v2_compts_1('#skF_3', g1_pre_topc(u1_struct_0(B_26), u1_pre_topc(B_26))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(B_26), u1_pre_topc(B_26))) | ~m1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'), B_26) | ~l1_pre_topc(B_26) | ~l1_pre_topc(k1_pre_topc('#skF_1', '#skF_3')))), inference(resolution, [status(thm)], [c_26, c_9808])).
% 33.97/22.08  tff(c_58727, plain, (![B_698]: (v2_compts_1('#skF_3', g1_pre_topc(u1_struct_0(B_698), u1_pre_topc(B_698))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(B_698), u1_pre_topc(B_698))) | ~m1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'), B_698) | ~l1_pre_topc(B_698))), inference(demodulation, [status(thm), theory('equality')], [c_123, c_9820])).
% 33.97/22.08  tff(c_58732, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~m1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'), '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_58727, c_423])).
% 33.97/22.08  tff(c_58853, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_114, c_1353, c_58732])).
% 33.97/22.08  tff(c_58855, plain, (v2_compts_1('#skF_3', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitRight, [status(thm)], [c_42])).
% 33.97/22.08  tff(c_38, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~v2_compts_1('#skF_2', '#skF_1') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))) | ~v2_compts_1('#skF_3', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_121])).
% 33.97/22.08  tff(c_58925, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~v2_compts_1('#skF_2', '#skF_1') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))))), inference(demodulation, [status(thm), theory('equality')], [c_58855, c_38])).
% 33.97/22.08  tff(c_58926, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))))), inference(splitLeft, [status(thm)], [c_58925])).
% 33.97/22.08  tff(c_59054, plain, (~m1_pre_topc('#skF_1', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(resolution, [status(thm)], [c_59021, c_58926])).
% 33.97/22.08  tff(c_59381, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitLeft, [status(thm)], [c_59054])).
% 33.97/22.08  tff(c_59384, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_90, c_59381])).
% 33.97/22.08  tff(c_59388, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_59384])).
% 33.97/22.08  tff(c_59390, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitRight, [status(thm)], [c_59054])).
% 33.97/22.08  tff(c_59192, plain, (![B_709, A_710]: (m1_subset_1(u1_struct_0(B_709), k1_zfmisc_1(u1_struct_0(A_710))) | ~m1_pre_topc(B_709, A_710) | ~l1_pre_topc(A_710))), inference(resolution, [status(thm)], [c_55, c_59001])).
% 33.97/22.08  tff(c_59571, plain, (![A_725]: (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_725))) | ~m1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'), A_725) | ~l1_pre_topc(A_725))), inference(superposition, [status(thm), theory('equality')], [c_146, c_59192])).
% 33.97/22.08  tff(c_59578, plain, (~m1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'), g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(resolution, [status(thm)], [c_59571, c_58926])).
% 33.97/22.08  tff(c_59615, plain, (~m1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'), g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_59390, c_59578])).
% 33.97/22.08  tff(c_59630, plain, (~m1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~l1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_26, c_59615])).
% 33.97/22.08  tff(c_59634, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_123, c_32, c_114, c_59630])).
% 33.97/22.08  tff(c_59635, plain, (~v2_compts_1('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_58925])).
% 33.97/22.08  tff(c_59656, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_59635])).
% 33.97/22.08  tff(c_59636, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))))), inference(splitRight, [status(thm)], [c_58925])).
% 33.97/22.08  tff(c_40, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))) | ~v2_compts_1('#skF_3', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_121])).
% 33.97/22.08  tff(c_59638, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))))), inference(demodulation, [status(thm), theory('equality')], [c_58855, c_40])).
% 33.97/22.08  tff(c_59639, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))))), inference(splitLeft, [status(thm)], [c_59638])).
% 33.97/22.08  tff(c_59653, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_59636, c_59639])).
% 33.97/22.08  tff(c_59655, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))))), inference(splitRight, [status(thm)], [c_59638])).
% 33.97/22.08  tff(c_12, plain, (![A_5, B_6]: (v1_pre_topc(k1_pre_topc(A_5, B_6)) | ~m1_subset_1(B_6, k1_zfmisc_1(u1_struct_0(A_5))) | ~l1_pre_topc(A_5))), inference(cnfTransformation, [status(thm)], [f_43])).
% 33.97/22.08  tff(c_59667, plain, (v1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_3')) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(resolution, [status(thm)], [c_59655, c_12])).
% 33.97/22.08  tff(c_60545, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitLeft, [status(thm)], [c_59667])).
% 33.97/22.08  tff(c_60548, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_90, c_60545])).
% 33.97/22.08  tff(c_60552, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_60548])).
% 33.97/22.08  tff(c_60554, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitRight, [status(thm)], [c_59667])).
% 33.97/22.08  tff(c_59654, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))))), inference(splitRight, [status(thm)], [c_59638])).
% 33.97/22.08  tff(c_59678, plain, (m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'), g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(resolution, [status(thm)], [c_59654, c_10])).
% 33.97/22.08  tff(c_62266, plain, (m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'), g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_60554, c_59678])).
% 33.97/22.08  tff(c_22, plain, (![B_23, A_21]: (m1_pre_topc(B_23, A_21) | ~m1_pre_topc(B_23, g1_pre_topc(u1_struct_0(A_21), u1_pre_topc(A_21))) | ~l1_pre_topc(A_21))), inference(cnfTransformation, [status(thm)], [f_78])).
% 33.97/22.08  tff(c_62271, plain, (m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_62266, c_22])).
% 33.97/22.08  tff(c_62280, plain, (m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_62271])).
% 33.97/22.08  tff(c_18, plain, (![A_11, B_13]: (u1_struct_0(k1_pre_topc(A_11, B_13))=B_13 | ~m1_subset_1(B_13, k1_zfmisc_1(u1_struct_0(A_11))) | ~l1_pre_topc(A_11))), inference(cnfTransformation, [status(thm)], [f_61])).
% 33.97/22.08  tff(c_59677, plain, (u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'))='#skF_2' | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(resolution, [status(thm)], [c_59654, c_18])).
% 33.97/22.08  tff(c_61116, plain, (u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_60554, c_59677])).
% 33.97/22.08  tff(c_59756, plain, (![C_727, A_728, B_729]: (m1_subset_1(C_727, k1_zfmisc_1(u1_struct_0(A_728))) | ~m1_subset_1(C_727, k1_zfmisc_1(u1_struct_0(B_729))) | ~m1_pre_topc(B_729, A_728) | ~l1_pre_topc(A_728))), inference(cnfTransformation, [status(thm)], [f_71])).
% 33.97/22.08  tff(c_59781, plain, (![B_729, A_728]: (m1_subset_1(u1_struct_0(B_729), k1_zfmisc_1(u1_struct_0(A_728))) | ~m1_pre_topc(B_729, A_728) | ~l1_pre_topc(A_728))), inference(resolution, [status(thm)], [c_55, c_59756])).
% 33.97/22.08  tff(c_64856, plain, (![A_833]: (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(A_833))) | ~m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'), A_833) | ~l1_pre_topc(A_833))), inference(superposition, [status(thm), theory('equality')], [c_61116, c_59781])).
% 33.97/22.08  tff(c_64859, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_62280, c_64856])).
% 33.97/22.08  tff(c_64873, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_64859])).
% 33.97/22.08  tff(c_64875, plain, $false, inference(negUnitSimplification, [status(thm)], [c_59656, c_64873])).
% 33.97/22.08  tff(c_64876, plain, (~v2_compts_1('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_59635])).
% 33.97/22.08  tff(c_64877, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_59635])).
% 33.97/22.08  tff(c_64882, plain, (m1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_64877, c_10])).
% 33.97/22.08  tff(c_64891, plain, (m1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_64882])).
% 33.97/22.08  tff(c_64908, plain, (l1_pre_topc(k1_pre_topc('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_64891, c_14])).
% 33.97/22.08  tff(c_64911, plain, (l1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_64908])).
% 33.97/22.08  tff(c_64880, plain, (u1_struct_0(k1_pre_topc('#skF_1', '#skF_2'))='#skF_2' | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_64877, c_18])).
% 33.97/22.08  tff(c_64888, plain, (u1_struct_0(k1_pre_topc('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_64880])).
% 33.97/22.08  tff(c_101, plain, (![A_59, B_60]: (m1_pre_topc(k1_pre_topc(A_59, B_60), A_59) | ~m1_subset_1(B_60, k1_zfmisc_1(u1_struct_0(A_59))) | ~l1_pre_topc(A_59))), inference(cnfTransformation, [status(thm)], [f_43])).
% 33.97/22.08  tff(c_105, plain, (![A_59]: (m1_pre_topc(k1_pre_topc(A_59, u1_struct_0(A_59)), A_59) | ~l1_pre_topc(A_59))), inference(resolution, [status(thm)], [c_55, c_101])).
% 33.97/22.08  tff(c_64932, plain, (m1_pre_topc(k1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'), '#skF_2'), k1_pre_topc('#skF_1', '#skF_2')) | ~l1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_64888, c_105])).
% 33.97/22.08  tff(c_64963, plain, (m1_pre_topc(k1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'), '#skF_2'), k1_pre_topc('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_64911, c_64932])).
% 33.97/22.08  tff(c_147, plain, (![A_65]: (u1_struct_0(k1_pre_topc(A_65, u1_struct_0(A_65)))=u1_struct_0(A_65) | ~l1_pre_topc(A_65))), inference(resolution, [status(thm)], [c_55, c_136])).
% 33.97/22.08  tff(c_64920, plain, (u1_struct_0(k1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'), '#skF_2'))=u1_struct_0(k1_pre_topc('#skF_1', '#skF_2')) | ~l1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_64888, c_147])).
% 33.97/22.08  tff(c_64955, plain, (u1_struct_0(k1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'), '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_64911, c_64888, c_64920])).
% 33.97/22.08  tff(c_65373, plain, (![D_842, B_843, A_844]: (v2_compts_1(D_842, B_843) | ~v2_compts_1(D_842, A_844) | ~m1_subset_1(D_842, k1_zfmisc_1(u1_struct_0(B_843))) | ~m1_subset_1(D_842, k1_zfmisc_1(u1_struct_0(A_844))) | ~m1_pre_topc(B_843, A_844) | ~l1_pre_topc(A_844))), inference(cnfTransformation, [status(thm)], [f_104])).
% 33.97/22.08  tff(c_67666, plain, (![B_902, A_903]: (v2_compts_1(u1_struct_0(B_902), B_902) | ~v2_compts_1(u1_struct_0(B_902), A_903) | ~m1_subset_1(u1_struct_0(B_902), k1_zfmisc_1(u1_struct_0(A_903))) | ~m1_pre_topc(B_902, A_903) | ~l1_pre_topc(A_903))), inference(resolution, [status(thm)], [c_55, c_65373])).
% 33.97/22.08  tff(c_67716, plain, (![B_902]: (v2_compts_1(u1_struct_0(B_902), B_902) | ~v2_compts_1(u1_struct_0(B_902), k1_pre_topc('#skF_1', '#skF_2')) | ~m1_subset_1(u1_struct_0(B_902), k1_zfmisc_1('#skF_2')) | ~m1_pre_topc(B_902, k1_pre_topc('#skF_1', '#skF_2')) | ~l1_pre_topc(k1_pre_topc('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_64888, c_67666])).
% 33.97/22.08  tff(c_78622, plain, (![B_1020]: (v2_compts_1(u1_struct_0(B_1020), B_1020) | ~v2_compts_1(u1_struct_0(B_1020), k1_pre_topc('#skF_1', '#skF_2')) | ~m1_subset_1(u1_struct_0(B_1020), k1_zfmisc_1('#skF_2')) | ~m1_pre_topc(B_1020, k1_pre_topc('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_64911, c_67716])).
% 33.97/22.08  tff(c_78674, plain, (v2_compts_1(u1_struct_0(k1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'), '#skF_2')), k1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'), '#skF_2')) | ~v2_compts_1('#skF_2', k1_pre_topc('#skF_1', '#skF_2')) | ~m1_subset_1(u1_struct_0(k1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'), '#skF_2')), k1_zfmisc_1('#skF_2')) | ~m1_pre_topc(k1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'), '#skF_2'), k1_pre_topc('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_64955, c_78622])).
% 33.97/22.08  tff(c_78708, plain, (v2_compts_1('#skF_2', k1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'), '#skF_2')) | ~v2_compts_1('#skF_2', k1_pre_topc('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_64963, c_55, c_64955, c_64955, c_78674])).
% 33.97/22.08  tff(c_78714, plain, (~v2_compts_1('#skF_2', k1_pre_topc('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_78708])).
% 33.97/22.08  tff(c_58854, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))) | v2_compts_1('#skF_2', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitRight, [status(thm)], [c_42])).
% 33.97/22.08  tff(c_64913, plain, (v2_compts_1('#skF_2', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_59636, c_58854])).
% 33.97/22.08  tff(c_65131, plain, (![C_834, A_835, B_836]: (m1_subset_1(C_834, k1_zfmisc_1(u1_struct_0(A_835))) | ~m1_subset_1(C_834, k1_zfmisc_1(u1_struct_0(B_836))) | ~m1_pre_topc(B_836, A_835) | ~l1_pre_topc(A_835))), inference(cnfTransformation, [status(thm)], [f_71])).
% 33.97/22.08  tff(c_65161, plain, (![A_835]: (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(A_835))) | ~m1_pre_topc('#skF_1', A_835) | ~l1_pre_topc(A_835))), inference(resolution, [status(thm)], [c_64877, c_65131])).
% 33.97/22.08  tff(c_65391, plain, (![A_844]: (v2_compts_1('#skF_2', '#skF_1') | ~v2_compts_1('#skF_2', A_844) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(A_844))) | ~m1_pre_topc('#skF_1', A_844) | ~l1_pre_topc(A_844))), inference(resolution, [status(thm)], [c_64877, c_65373])).
% 33.97/22.08  tff(c_65936, plain, (![A_867]: (~v2_compts_1('#skF_2', A_867) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(A_867))) | ~m1_pre_topc('#skF_1', A_867) | ~l1_pre_topc(A_867))), inference(negUnitSimplification, [status(thm)], [c_64876, c_65391])).
% 33.97/22.08  tff(c_65997, plain, (![A_868]: (~v2_compts_1('#skF_2', A_868) | ~m1_pre_topc('#skF_1', A_868) | ~l1_pre_topc(A_868))), inference(resolution, [status(thm)], [c_65161, c_65936])).
% 33.97/22.08  tff(c_66001, plain, (~m1_pre_topc('#skF_1', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(resolution, [status(thm)], [c_64913, c_65997])).
% 33.97/22.08  tff(c_66148, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitLeft, [status(thm)], [c_66001])).
% 33.97/22.08  tff(c_66151, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_90, c_66148])).
% 33.97/22.08  tff(c_66155, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_66151])).
% 33.97/22.08  tff(c_66157, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitRight, [status(thm)], [c_66001])).
% 33.97/22.08  tff(c_85212, plain, (![D_1104, A_1105]: (v2_compts_1(D_1104, k1_pre_topc('#skF_1', '#skF_2')) | ~v2_compts_1(D_1104, A_1105) | ~m1_subset_1(D_1104, k1_zfmisc_1('#skF_2')) | ~m1_subset_1(D_1104, k1_zfmisc_1(u1_struct_0(A_1105))) | ~m1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'), A_1105) | ~l1_pre_topc(A_1105))), inference(superposition, [status(thm), theory('equality')], [c_64888, c_65373])).
% 33.97/22.08  tff(c_85356, plain, (v2_compts_1('#skF_2', k1_pre_topc('#skF_1', '#skF_2')) | ~v2_compts_1('#skF_2', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1('#skF_2')) | ~m1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'), g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(resolution, [status(thm)], [c_59654, c_85212])).
% 33.97/22.08  tff(c_85465, plain, (v2_compts_1('#skF_2', k1_pre_topc('#skF_1', '#skF_2')) | ~m1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'), g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_66157, c_55, c_64913, c_85356])).
% 33.97/22.08  tff(c_85466, plain, (~m1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'), g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_78714, c_85465])).
% 33.97/22.08  tff(c_85491, plain, (~m1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~l1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_26, c_85466])).
% 33.97/22.08  tff(c_85495, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64911, c_32, c_64891, c_85491])).
% 33.97/22.08  tff(c_85497, plain, (v2_compts_1('#skF_2', k1_pre_topc('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_78708])).
% 33.97/22.08  tff(c_65559, plain, (![D_852, A_853, B_854]: (v2_compts_1(D_852, A_853) | ~v2_compts_1(D_852, B_854) | ~m1_subset_1(D_852, k1_zfmisc_1(u1_struct_0(B_854))) | ~m1_subset_1(D_852, k1_zfmisc_1(u1_struct_0(A_853))) | ~m1_pre_topc(B_854, A_853) | ~l1_pre_topc(A_853))), inference(cnfTransformation, [status(thm)], [f_104])).
% 33.97/22.08  tff(c_67354, plain, (![B_895, A_896]: (v2_compts_1(u1_struct_0(B_895), A_896) | ~v2_compts_1(u1_struct_0(B_895), B_895) | ~m1_subset_1(u1_struct_0(B_895), k1_zfmisc_1(u1_struct_0(A_896))) | ~m1_pre_topc(B_895, A_896) | ~l1_pre_topc(A_896))), inference(resolution, [status(thm)], [c_55, c_65559])).
% 33.97/22.08  tff(c_67376, plain, (![A_896]: (v2_compts_1(u1_struct_0(k1_pre_topc('#skF_1', '#skF_2')), A_896) | ~v2_compts_1('#skF_2', k1_pre_topc('#skF_1', '#skF_2')) | ~m1_subset_1(u1_struct_0(k1_pre_topc('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0(A_896))) | ~m1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'), A_896) | ~l1_pre_topc(A_896))), inference(superposition, [status(thm), theory('equality')], [c_64888, c_67354])).
% 33.97/22.08  tff(c_67393, plain, (![A_896]: (v2_compts_1('#skF_2', A_896) | ~v2_compts_1('#skF_2', k1_pre_topc('#skF_1', '#skF_2')) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(A_896))) | ~m1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'), A_896) | ~l1_pre_topc(A_896))), inference(demodulation, [status(thm), theory('equality')], [c_64888, c_64888, c_67376])).
% 33.97/22.08  tff(c_85603, plain, (![A_1108]: (v2_compts_1('#skF_2', A_1108) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(A_1108))) | ~m1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'), A_1108) | ~l1_pre_topc(A_1108))), inference(demodulation, [status(thm), theory('equality')], [c_85497, c_67393])).
% 33.97/22.08  tff(c_85710, plain, (v2_compts_1('#skF_2', '#skF_1') | ~m1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_64877, c_85603])).
% 33.97/22.08  tff(c_85771, plain, (v2_compts_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_64891, c_85710])).
% 33.97/22.08  tff(c_85773, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64876, c_85771])).
% 33.97/22.08  tff(c_85775, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_48])).
% 33.97/22.08  tff(c_44, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~v2_compts_1('#skF_2', '#skF_1') | m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_121])).
% 33.97/22.08  tff(c_85839, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~v2_compts_1('#skF_2', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_85775, c_44])).
% 33.97/22.08  tff(c_85840, plain, (~v2_compts_1('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_85839])).
% 33.97/22.08  tff(c_46, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))) | m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_121])).
% 33.97/22.08  tff(c_85853, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))))), inference(negUnitSimplification, [status(thm)], [c_85775, c_46])).
% 33.97/22.08  tff(c_85864, plain, (v1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(resolution, [status(thm)], [c_85853, c_12])).
% 33.97/22.08  tff(c_85865, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitLeft, [status(thm)], [c_85864])).
% 33.97/22.08  tff(c_85869, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_90, c_85865])).
% 33.97/22.08  tff(c_85873, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_85869])).
% 33.97/22.08  tff(c_85875, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitRight, [status(thm)], [c_85864])).
% 33.97/22.08  tff(c_85863, plain, (m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'), g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(resolution, [status(thm)], [c_85853, c_10])).
% 33.97/22.08  tff(c_86326, plain, (m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'), g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_85875, c_85863])).
% 33.97/22.08  tff(c_86343, plain, (m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_86326, c_22])).
% 33.97/22.08  tff(c_86364, plain, (m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_86343])).
% 33.97/22.08  tff(c_85862, plain, (u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'))='#skF_2' | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(resolution, [status(thm)], [c_85853, c_18])).
% 33.97/22.08  tff(c_86034, plain, (u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_85875, c_85862])).
% 33.97/22.08  tff(c_85876, plain, (![C_1118, A_1119, B_1120]: (m1_subset_1(C_1118, k1_zfmisc_1(u1_struct_0(A_1119))) | ~m1_subset_1(C_1118, k1_zfmisc_1(u1_struct_0(B_1120))) | ~m1_pre_topc(B_1120, A_1119) | ~l1_pre_topc(A_1119))), inference(cnfTransformation, [status(thm)], [f_71])).
% 33.97/22.08  tff(c_85885, plain, (![B_1120, A_1119]: (m1_subset_1(u1_struct_0(B_1120), k1_zfmisc_1(u1_struct_0(A_1119))) | ~m1_pre_topc(B_1120, A_1119) | ~l1_pre_topc(A_1119))), inference(resolution, [status(thm)], [c_55, c_85876])).
% 33.97/22.08  tff(c_86052, plain, (![A_1119]: (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(A_1119))) | ~m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'), A_1119) | ~l1_pre_topc(A_1119))), inference(superposition, [status(thm), theory('equality')], [c_86034, c_85885])).
% 33.97/22.08  tff(c_86374, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_86364, c_86052])).
% 33.97/22.08  tff(c_86391, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_86374])).
% 33.97/22.08  tff(c_85774, plain, (v2_compts_1('#skF_2', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitRight, [status(thm)], [c_48])).
% 33.97/22.08  tff(c_85907, plain, (![D_1123, A_1124, B_1125]: (v2_compts_1(D_1123, A_1124) | ~v2_compts_1(D_1123, B_1125) | ~m1_subset_1(D_1123, k1_zfmisc_1(u1_struct_0(B_1125))) | ~m1_subset_1(D_1123, k1_zfmisc_1(u1_struct_0(A_1124))) | ~m1_pre_topc(B_1125, A_1124) | ~l1_pre_topc(A_1124))), inference(cnfTransformation, [status(thm)], [f_104])).
% 33.97/22.08  tff(c_86782, plain, (![B_1159, A_1160]: (v2_compts_1(u1_struct_0(B_1159), A_1160) | ~v2_compts_1(u1_struct_0(B_1159), B_1159) | ~m1_subset_1(u1_struct_0(B_1159), k1_zfmisc_1(u1_struct_0(A_1160))) | ~m1_pre_topc(B_1159, A_1160) | ~l1_pre_topc(A_1160))), inference(resolution, [status(thm)], [c_55, c_85907])).
% 33.97/22.08  tff(c_86788, plain, (![A_1160]: (v2_compts_1(u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')), A_1160) | ~v2_compts_1('#skF_2', k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')) | ~m1_subset_1(u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')), k1_zfmisc_1(u1_struct_0(A_1160))) | ~m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'), A_1160) | ~l1_pre_topc(A_1160))), inference(superposition, [status(thm), theory('equality')], [c_86034, c_86782])).
% 33.97/22.08  tff(c_86795, plain, (![A_1160]: (v2_compts_1('#skF_2', A_1160) | ~v2_compts_1('#skF_2', k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(A_1160))) | ~m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'), A_1160) | ~l1_pre_topc(A_1160))), inference(demodulation, [status(thm), theory('equality')], [c_86034, c_86034, c_86788])).
% 33.97/22.08  tff(c_95017, plain, (~v2_compts_1('#skF_2', k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'))), inference(splitLeft, [status(thm)], [c_86795])).
% 33.97/22.08  tff(c_86144, plain, (![D_1138, B_1139, A_1140]: (v2_compts_1(D_1138, B_1139) | ~v2_compts_1(D_1138, A_1140) | ~m1_subset_1(D_1138, k1_zfmisc_1(u1_struct_0(B_1139))) | ~m1_subset_1(D_1138, k1_zfmisc_1(u1_struct_0(A_1140))) | ~m1_pre_topc(B_1139, A_1140) | ~l1_pre_topc(A_1140))), inference(cnfTransformation, [status(thm)], [f_104])).
% 33.97/22.08  tff(c_86840, plain, (![B_1162, A_1163]: (v2_compts_1(u1_struct_0(B_1162), B_1162) | ~v2_compts_1(u1_struct_0(B_1162), A_1163) | ~m1_subset_1(u1_struct_0(B_1162), k1_zfmisc_1(u1_struct_0(A_1163))) | ~m1_pre_topc(B_1162, A_1163) | ~l1_pre_topc(A_1163))), inference(resolution, [status(thm)], [c_55, c_86144])).
% 33.97/22.08  tff(c_86850, plain, (![A_1163]: (v2_compts_1(u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')), k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')) | ~v2_compts_1(u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')), A_1163) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(A_1163))) | ~m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'), A_1163) | ~l1_pre_topc(A_1163))), inference(superposition, [status(thm), theory('equality')], [c_86034, c_86840])).
% 33.97/22.08  tff(c_86872, plain, (![A_1163]: (v2_compts_1('#skF_2', k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')) | ~v2_compts_1('#skF_2', A_1163) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(A_1163))) | ~m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'), A_1163) | ~l1_pre_topc(A_1163))), inference(demodulation, [status(thm), theory('equality')], [c_86034, c_86034, c_86850])).
% 33.97/22.08  tff(c_95386, plain, (![A_1271]: (~v2_compts_1('#skF_2', A_1271) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(A_1271))) | ~m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'), A_1271) | ~l1_pre_topc(A_1271))), inference(negUnitSimplification, [status(thm)], [c_95017, c_86872])).
% 33.97/22.08  tff(c_95408, plain, (~v2_compts_1('#skF_2', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(resolution, [status(thm)], [c_86326, c_95386])).
% 33.97/22.08  tff(c_95431, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_85875, c_85853, c_85774, c_95408])).
% 33.97/22.08  tff(c_95807, plain, (![A_1278]: (v2_compts_1('#skF_2', A_1278) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(A_1278))) | ~m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'), A_1278) | ~l1_pre_topc(A_1278))), inference(splitRight, [status(thm)], [c_86795])).
% 33.97/22.08  tff(c_95826, plain, (v2_compts_1('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_86364, c_95807])).
% 33.97/22.08  tff(c_95848, plain, (v2_compts_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_86391, c_95826])).
% 33.97/22.08  tff(c_95850, plain, $false, inference(negUnitSimplification, [status(thm)], [c_85840, c_95848])).
% 33.97/22.08  tff(c_95851, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_85839])).
% 33.97/22.08  tff(c_95853, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))))), inference(negUnitSimplification, [status(thm)], [c_85775, c_46])).
% 33.97/22.08  tff(c_95864, plain, (v1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(resolution, [status(thm)], [c_95853, c_12])).
% 33.97/22.08  tff(c_95878, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitLeft, [status(thm)], [c_95864])).
% 33.97/22.08  tff(c_95881, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_90, c_95878])).
% 33.97/22.08  tff(c_95885, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_95881])).
% 33.97/22.08  tff(c_95887, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitRight, [status(thm)], [c_95864])).
% 33.97/22.08  tff(c_95863, plain, (m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'), g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(resolution, [status(thm)], [c_95853, c_10])).
% 33.97/22.08  tff(c_96333, plain, (m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'), g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_95887, c_95863])).
% 33.97/22.08  tff(c_96347, plain, (m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_96333, c_22])).
% 33.97/22.08  tff(c_96365, plain, (m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_96347])).
% 33.97/22.08  tff(c_95862, plain, (u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'))='#skF_2' | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(resolution, [status(thm)], [c_95853, c_18])).
% 33.97/22.08  tff(c_96030, plain, (u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_95887, c_95862])).
% 33.97/22.08  tff(c_95888, plain, (![C_1281, A_1282, B_1283]: (m1_subset_1(C_1281, k1_zfmisc_1(u1_struct_0(A_1282))) | ~m1_subset_1(C_1281, k1_zfmisc_1(u1_struct_0(B_1283))) | ~m1_pre_topc(B_1283, A_1282) | ~l1_pre_topc(A_1282))), inference(cnfTransformation, [status(thm)], [f_71])).
% 33.97/22.08  tff(c_95897, plain, (![B_1283, A_1282]: (m1_subset_1(u1_struct_0(B_1283), k1_zfmisc_1(u1_struct_0(A_1282))) | ~m1_pre_topc(B_1283, A_1282) | ~l1_pre_topc(A_1282))), inference(resolution, [status(thm)], [c_55, c_95888])).
% 33.97/22.08  tff(c_96046, plain, (![A_1282]: (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(A_1282))) | ~m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'), A_1282) | ~l1_pre_topc(A_1282))), inference(superposition, [status(thm), theory('equality')], [c_96030, c_95897])).
% 33.97/22.08  tff(c_96372, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_96365, c_96046])).
% 33.97/22.08  tff(c_96386, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_96372])).
% 33.97/22.08  tff(c_96388, plain, $false, inference(negUnitSimplification, [status(thm)], [c_95851, c_96386])).
% 33.97/22.08  tff(c_96390, plain, (~v2_compts_1('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_54])).
% 33.97/22.08  tff(c_50, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~v2_compts_1('#skF_2', '#skF_1') | v2_compts_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_121])).
% 33.97/22.08  tff(c_96403, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~v2_compts_1('#skF_2', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_96390, c_50])).
% 33.97/22.08  tff(c_96404, plain, (~v2_compts_1('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_96403])).
% 33.97/22.08  tff(c_96392, plain, (![A_1320]: (m1_subset_1(u1_pre_topc(A_1320), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_1320)))) | ~l1_pre_topc(A_1320))), inference(cnfTransformation, [status(thm)], [f_54])).
% 33.97/22.08  tff(c_96400, plain, (![A_1320]: (l1_pre_topc(g1_pre_topc(u1_struct_0(A_1320), u1_pre_topc(A_1320))) | ~l1_pre_topc(A_1320))), inference(resolution, [status(thm)], [c_96392, c_6])).
% 33.97/22.08  tff(c_52, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))) | v2_compts_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_121])).
% 33.97/22.08  tff(c_96414, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))))), inference(negUnitSimplification, [status(thm)], [c_96390, c_52])).
% 33.97/22.08  tff(c_96418, plain, (v1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(resolution, [status(thm)], [c_96414, c_12])).
% 33.97/22.08  tff(c_96505, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitLeft, [status(thm)], [c_96418])).
% 33.97/22.08  tff(c_96518, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_96400, c_96505])).
% 33.97/22.08  tff(c_96522, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_96518])).
% 33.97/22.08  tff(c_96524, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitRight, [status(thm)], [c_96418])).
% 33.97/22.08  tff(c_96419, plain, (![A_1328, B_1329]: (m1_pre_topc(k1_pre_topc(A_1328, B_1329), A_1328) | ~m1_subset_1(B_1329, k1_zfmisc_1(u1_struct_0(A_1328))) | ~l1_pre_topc(A_1328))), inference(cnfTransformation, [status(thm)], [f_43])).
% 33.97/22.08  tff(c_96425, plain, (m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'), g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(resolution, [status(thm)], [c_96414, c_96419])).
% 33.97/22.08  tff(c_97091, plain, (m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'), g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_96524, c_96425])).
% 33.97/22.08  tff(c_97110, plain, (m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_97091, c_22])).
% 33.97/22.08  tff(c_97134, plain, (m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_97110])).
% 33.97/22.08  tff(c_96438, plain, (![A_1332, B_1333]: (u1_struct_0(k1_pre_topc(A_1332, B_1333))=B_1333 | ~m1_subset_1(B_1333, k1_zfmisc_1(u1_struct_0(A_1332))) | ~l1_pre_topc(A_1332))), inference(cnfTransformation, [status(thm)], [f_61])).
% 33.97/22.08  tff(c_96446, plain, (u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'))='#skF_2' | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(resolution, [status(thm)], [c_96414, c_96438])).
% 33.97/22.08  tff(c_96683, plain, (u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_96524, c_96446])).
% 33.97/22.08  tff(c_96526, plain, (![C_1340, A_1341, B_1342]: (m1_subset_1(C_1340, k1_zfmisc_1(u1_struct_0(A_1341))) | ~m1_subset_1(C_1340, k1_zfmisc_1(u1_struct_0(B_1342))) | ~m1_pre_topc(B_1342, A_1341) | ~l1_pre_topc(A_1341))), inference(cnfTransformation, [status(thm)], [f_71])).
% 33.97/22.08  tff(c_96535, plain, (![B_1342, A_1341]: (m1_subset_1(u1_struct_0(B_1342), k1_zfmisc_1(u1_struct_0(A_1341))) | ~m1_pre_topc(B_1342, A_1341) | ~l1_pre_topc(A_1341))), inference(resolution, [status(thm)], [c_55, c_96526])).
% 33.97/22.08  tff(c_96701, plain, (![A_1341]: (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(A_1341))) | ~m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'), A_1341) | ~l1_pre_topc(A_1341))), inference(superposition, [status(thm), theory('equality')], [c_96683, c_96535])).
% 33.97/22.08  tff(c_97147, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_97134, c_96701])).
% 33.97/22.08  tff(c_97168, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_97147])).
% 33.97/22.08  tff(c_96389, plain, (v2_compts_1('#skF_2', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitRight, [status(thm)], [c_54])).
% 33.97/22.08  tff(c_96578, plain, (![D_1351, A_1352, B_1353]: (v2_compts_1(D_1351, A_1352) | ~v2_compts_1(D_1351, B_1353) | ~m1_subset_1(D_1351, k1_zfmisc_1(u1_struct_0(B_1353))) | ~m1_subset_1(D_1351, k1_zfmisc_1(u1_struct_0(A_1352))) | ~m1_pre_topc(B_1353, A_1352) | ~l1_pre_topc(A_1352))), inference(cnfTransformation, [status(thm)], [f_104])).
% 33.97/22.08  tff(c_97640, plain, (![B_1387, A_1388]: (v2_compts_1(u1_struct_0(B_1387), A_1388) | ~v2_compts_1(u1_struct_0(B_1387), B_1387) | ~m1_subset_1(u1_struct_0(B_1387), k1_zfmisc_1(u1_struct_0(A_1388))) | ~m1_pre_topc(B_1387, A_1388) | ~l1_pre_topc(A_1388))), inference(resolution, [status(thm)], [c_55, c_96578])).
% 33.97/22.08  tff(c_97646, plain, (![A_1388]: (v2_compts_1(u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')), A_1388) | ~v2_compts_1('#skF_2', k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')) | ~m1_subset_1(u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')), k1_zfmisc_1(u1_struct_0(A_1388))) | ~m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'), A_1388) | ~l1_pre_topc(A_1388))), inference(superposition, [status(thm), theory('equality')], [c_96683, c_97640])).
% 33.97/22.08  tff(c_97653, plain, (![A_1388]: (v2_compts_1('#skF_2', A_1388) | ~v2_compts_1('#skF_2', k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(A_1388))) | ~m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'), A_1388) | ~l1_pre_topc(A_1388))), inference(demodulation, [status(thm), theory('equality')], [c_96683, c_96683, c_97646])).
% 33.97/22.08  tff(c_104798, plain, (~v2_compts_1('#skF_2', k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'))), inference(splitLeft, [status(thm)], [c_97653])).
% 33.97/22.08  tff(c_96826, plain, (![D_1363, B_1364, A_1365]: (v2_compts_1(D_1363, B_1364) | ~v2_compts_1(D_1363, A_1365) | ~m1_subset_1(D_1363, k1_zfmisc_1(u1_struct_0(B_1364))) | ~m1_subset_1(D_1363, k1_zfmisc_1(u1_struct_0(A_1365))) | ~m1_pre_topc(B_1364, A_1365) | ~l1_pre_topc(A_1365))), inference(cnfTransformation, [status(thm)], [f_104])).
% 33.97/22.08  tff(c_97387, plain, (![B_1384, A_1385]: (v2_compts_1(u1_struct_0(B_1384), B_1384) | ~v2_compts_1(u1_struct_0(B_1384), A_1385) | ~m1_subset_1(u1_struct_0(B_1384), k1_zfmisc_1(u1_struct_0(A_1385))) | ~m1_pre_topc(B_1384, A_1385) | ~l1_pre_topc(A_1385))), inference(resolution, [status(thm)], [c_55, c_96826])).
% 33.97/22.08  tff(c_97393, plain, (![A_1385]: (v2_compts_1(u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')), k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')) | ~v2_compts_1(u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')), A_1385) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(A_1385))) | ~m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'), A_1385) | ~l1_pre_topc(A_1385))), inference(superposition, [status(thm), theory('equality')], [c_96683, c_97387])).
% 33.97/22.08  tff(c_97412, plain, (![A_1385]: (v2_compts_1('#skF_2', k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')) | ~v2_compts_1('#skF_2', A_1385) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(A_1385))) | ~m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'), A_1385) | ~l1_pre_topc(A_1385))), inference(demodulation, [status(thm), theory('equality')], [c_96683, c_96683, c_97393])).
% 33.97/22.08  tff(c_105150, plain, (![A_1485]: (~v2_compts_1('#skF_2', A_1485) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(A_1485))) | ~m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'), A_1485) | ~l1_pre_topc(A_1485))), inference(negUnitSimplification, [status(thm)], [c_104798, c_97412])).
% 33.97/22.08  tff(c_105172, plain, (~v2_compts_1('#skF_2', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(resolution, [status(thm)], [c_97091, c_105150])).
% 33.97/22.08  tff(c_105195, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_96524, c_96414, c_96389, c_105172])).
% 33.97/22.08  tff(c_105554, plain, (![A_1486]: (v2_compts_1('#skF_2', A_1486) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(A_1486))) | ~m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'), A_1486) | ~l1_pre_topc(A_1486))), inference(splitRight, [status(thm)], [c_97653])).
% 33.97/22.08  tff(c_105573, plain, (v2_compts_1('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_97134, c_105554])).
% 33.97/22.08  tff(c_105595, plain, (v2_compts_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_97168, c_105573])).
% 33.97/22.08  tff(c_105597, plain, $false, inference(negUnitSimplification, [status(thm)], [c_96404, c_105595])).
% 33.97/22.08  tff(c_105598, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_96403])).
% 33.97/22.08  tff(c_105675, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))))), inference(negUnitSimplification, [status(thm)], [c_96390, c_52])).
% 33.97/22.08  tff(c_105686, plain, (v1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(resolution, [status(thm)], [c_105675, c_12])).
% 33.97/22.08  tff(c_105702, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitLeft, [status(thm)], [c_105686])).
% 33.97/22.08  tff(c_105705, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_96400, c_105702])).
% 33.97/22.08  tff(c_105709, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_105705])).
% 33.97/22.08  tff(c_105711, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitRight, [status(thm)], [c_105686])).
% 33.97/22.08  tff(c_105684, plain, (m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'), g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(resolution, [status(thm)], [c_105675, c_10])).
% 33.97/22.08  tff(c_106382, plain, (m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'), g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_105711, c_105684])).
% 33.97/22.08  tff(c_106401, plain, (m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_106382, c_22])).
% 33.97/22.08  tff(c_106425, plain, (m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_106401])).
% 33.97/22.08  tff(c_105685, plain, (u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'))='#skF_2' | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(resolution, [status(thm)], [c_105675, c_18])).
% 33.97/22.08  tff(c_105853, plain, (u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_105711, c_105685])).
% 33.97/22.08  tff(c_105712, plain, (![C_1501, A_1502, B_1503]: (m1_subset_1(C_1501, k1_zfmisc_1(u1_struct_0(A_1502))) | ~m1_subset_1(C_1501, k1_zfmisc_1(u1_struct_0(B_1503))) | ~m1_pre_topc(B_1503, A_1502) | ~l1_pre_topc(A_1502))), inference(cnfTransformation, [status(thm)], [f_71])).
% 33.97/22.08  tff(c_105721, plain, (![B_1503, A_1502]: (m1_subset_1(u1_struct_0(B_1503), k1_zfmisc_1(u1_struct_0(A_1502))) | ~m1_pre_topc(B_1503, A_1502) | ~l1_pre_topc(A_1502))), inference(resolution, [status(thm)], [c_55, c_105712])).
% 33.97/22.08  tff(c_105869, plain, (![A_1502]: (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(A_1502))) | ~m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'), A_1502) | ~l1_pre_topc(A_1502))), inference(superposition, [status(thm), theory('equality')], [c_105853, c_105721])).
% 33.97/22.08  tff(c_106440, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_106425, c_105869])).
% 33.97/22.08  tff(c_106461, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_106440])).
% 33.97/22.08  tff(c_106463, plain, $false, inference(negUnitSimplification, [status(thm)], [c_105598, c_106461])).
% 33.97/22.08  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 33.97/22.08  
% 33.97/22.08  Inference rules
% 33.97/22.08  ----------------------
% 33.97/22.08  #Ref     : 0
% 33.97/22.08  #Sup     : 25262
% 33.97/22.08  #Fact    : 0
% 33.97/22.08  #Define  : 0
% 33.97/22.08  #Split   : 90
% 33.97/22.08  #Chain   : 0
% 33.97/22.08  #Close   : 0
% 33.97/22.08  
% 33.97/22.09  Ordering : KBO
% 33.97/22.09  
% 33.97/22.09  Simplification rules
% 33.97/22.09  ----------------------
% 33.97/22.09  #Subsume      : 3731
% 33.97/22.09  #Demod        : 32164
% 33.97/22.09  #Tautology    : 5384
% 33.97/22.09  #SimpNegUnit  : 31
% 33.97/22.09  #BackRed      : 0
% 33.97/22.09  
% 33.97/22.09  #Partial instantiations: 0
% 33.97/22.09  #Strategies tried      : 1
% 33.97/22.09  
% 33.97/22.09  Timing (in seconds)
% 33.97/22.09  ----------------------
% 33.97/22.09  Preprocessing        : 0.31
% 33.97/22.09  Parsing              : 0.17
% 33.97/22.09  CNF conversion       : 0.02
% 33.97/22.09  Main loop            : 20.97
% 33.97/22.09  Inferencing          : 2.74
% 33.97/22.09  Reduction            : 9.01
% 33.97/22.09  Demodulation         : 7.52
% 33.97/22.09  BG Simplification    : 0.33
% 33.97/22.09  Subsumption          : 7.79
% 33.97/22.09  Abstraction          : 0.51
% 33.97/22.09  MUC search           : 0.00
% 33.97/22.09  Cooper               : 0.00
% 33.97/22.09  Total                : 21.37
% 33.97/22.09  Index Insertion      : 0.00
% 33.97/22.09  Index Deletion       : 0.00
% 33.97/22.09  Index Matching       : 0.00
% 33.97/22.09  BG Taut test         : 0.00
%------------------------------------------------------------------------------
