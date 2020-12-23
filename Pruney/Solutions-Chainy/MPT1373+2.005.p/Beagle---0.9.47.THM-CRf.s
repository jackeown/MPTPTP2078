%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:01 EST 2020

% Result     : Theorem 25.35s
% Output     : CNFRefutation 25.39s
% Verified   : 
% Statistics : Number of formulae       :  141 ( 412 expanded)
%              Number of leaves         :   32 ( 151 expanded)
%              Depth                    :   17
%              Number of atoms          :  340 (1187 expanded)
%              Number of equality atoms :   19 ( 104 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_compts_1 > v1_tops_1 > r1_tarski > m1_subset_1 > m1_pre_topc > l1_pre_topc > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_compts_1,type,(
    v2_compts_1: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_tops_1,type,(
    v1_tops_1: ( $i * $i ) > $o )).

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

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_130,negated_conjecture,(
    ~ ! [A] :
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

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_46,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_33,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_35,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_79,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ? [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
          & v1_tops_1(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc4_tops_1)).

tff(f_93,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( v1_tops_1(B,A)
                  & r1_tarski(B,C) )
               => v1_tops_1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_tops_1)).

tff(f_72,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> k2_pre_topc(A,B) = k2_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tops_1)).

tff(f_63,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(B,k2_pre_topc(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_pre_topc)).

tff(f_56,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B)))
             => m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_pre_topc)).

tff(f_112,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( r1_tarski(C,k2_struct_0(B))
               => ( v2_compts_1(C,A)
                <=> ! [D] :
                      ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(B)))
                     => ( D = C
                       => v2_compts_1(D,B) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_compts_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(c_38,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_67532,plain,(
    ! [A_1891,B_1892] :
      ( r1_tarski(A_1891,B_1892)
      | ~ m1_subset_1(A_1891,k1_zfmisc_1(B_1892)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_67546,plain,(
    r1_tarski('#skF_6',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_38,c_67532])).

tff(c_44,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_42,plain,(
    m1_pre_topc('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_36,plain,(
    '#skF_5' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_52,plain,
    ( v2_compts_1('#skF_5','#skF_3')
    | v2_compts_1('#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_55,plain,
    ( v2_compts_1('#skF_6','#skF_3')
    | v2_compts_1('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_52])).

tff(c_72,plain,(
    v2_compts_1('#skF_6','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_55])).

tff(c_46,plain,
    ( ~ v2_compts_1('#skF_6','#skF_4')
    | ~ v2_compts_1('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_53,plain,
    ( ~ v2_compts_1('#skF_6','#skF_4')
    | ~ v2_compts_1('#skF_6','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_46])).

tff(c_73,plain,(
    ~ v2_compts_1('#skF_6','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_53])).

tff(c_40,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_54,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_40])).

tff(c_82,plain,(
    ! [A_73,B_74] :
      ( r1_tarski(A_73,B_74)
      | ~ m1_subset_1(A_73,k1_zfmisc_1(B_74)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_96,plain,(
    r1_tarski('#skF_6',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_38,c_82])).

tff(c_74,plain,(
    ! [B_69,A_70] :
      ( l1_pre_topc(B_69)
      | ~ m1_pre_topc(B_69,A_70)
      | ~ l1_pre_topc(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_77,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_74])).

tff(c_80,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_77])).

tff(c_4,plain,(
    ! [A_4] : k2_subset_1(A_4) = A_4 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_6,plain,(
    ! [A_5] : m1_subset_1(k2_subset_1(A_5),k1_zfmisc_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_56,plain,(
    ! [A_5] : m1_subset_1(A_5,k1_zfmisc_1(A_5)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_6])).

tff(c_98,plain,(
    ! [A_5] : r1_tarski(A_5,A_5) ),
    inference(resolution,[status(thm)],[c_56,c_82])).

tff(c_22,plain,(
    ! [A_24] :
      ( v1_tops_1('#skF_1'(A_24),A_24)
      | ~ l1_pre_topc(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_24,plain,(
    ! [A_24] :
      ( m1_subset_1('#skF_1'(A_24),k1_zfmisc_1(u1_struct_0(A_24)))
      | ~ l1_pre_topc(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_100,plain,(
    ! [A_76] :
      ( m1_subset_1('#skF_1'(A_76),k1_zfmisc_1(u1_struct_0(A_76)))
      | ~ l1_pre_topc(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(A_6,B_7)
      | ~ m1_subset_1(A_6,k1_zfmisc_1(B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_104,plain,(
    ! [A_76] :
      ( r1_tarski('#skF_1'(A_76),u1_struct_0(A_76))
      | ~ l1_pre_topc(A_76) ) ),
    inference(resolution,[status(thm)],[c_100,c_8])).

tff(c_719,plain,(
    ! [C_130,A_131,B_132] :
      ( v1_tops_1(C_130,A_131)
      | ~ r1_tarski(B_132,C_130)
      | ~ v1_tops_1(B_132,A_131)
      | ~ m1_subset_1(C_130,k1_zfmisc_1(u1_struct_0(A_131)))
      | ~ m1_subset_1(B_132,k1_zfmisc_1(u1_struct_0(A_131)))
      | ~ l1_pre_topc(A_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_25122,plain,(
    ! [A_976,A_977] :
      ( v1_tops_1(u1_struct_0(A_976),A_977)
      | ~ v1_tops_1('#skF_1'(A_976),A_977)
      | ~ m1_subset_1(u1_struct_0(A_976),k1_zfmisc_1(u1_struct_0(A_977)))
      | ~ m1_subset_1('#skF_1'(A_976),k1_zfmisc_1(u1_struct_0(A_977)))
      | ~ l1_pre_topc(A_977)
      | ~ l1_pre_topc(A_976) ) ),
    inference(resolution,[status(thm)],[c_104,c_719])).

tff(c_32864,plain,(
    ! [A_1245] :
      ( v1_tops_1(u1_struct_0(A_1245),A_1245)
      | ~ v1_tops_1('#skF_1'(A_1245),A_1245)
      | ~ m1_subset_1('#skF_1'(A_1245),k1_zfmisc_1(u1_struct_0(A_1245)))
      | ~ l1_pre_topc(A_1245) ) ),
    inference(resolution,[status(thm)],[c_56,c_25122])).

tff(c_32902,plain,(
    ! [A_1246] :
      ( v1_tops_1(u1_struct_0(A_1246),A_1246)
      | ~ v1_tops_1('#skF_1'(A_1246),A_1246)
      | ~ l1_pre_topc(A_1246) ) ),
    inference(resolution,[status(thm)],[c_24,c_32864])).

tff(c_273,plain,(
    ! [A_97,B_98] :
      ( k2_pre_topc(A_97,B_98) = k2_struct_0(A_97)
      | ~ v1_tops_1(B_98,A_97)
      | ~ m1_subset_1(B_98,k1_zfmisc_1(u1_struct_0(A_97)))
      | ~ l1_pre_topc(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_299,plain,(
    ! [A_97] :
      ( k2_pre_topc(A_97,u1_struct_0(A_97)) = k2_struct_0(A_97)
      | ~ v1_tops_1(u1_struct_0(A_97),A_97)
      | ~ l1_pre_topc(A_97) ) ),
    inference(resolution,[status(thm)],[c_56,c_273])).

tff(c_32960,plain,(
    ! [A_1250] :
      ( k2_pre_topc(A_1250,u1_struct_0(A_1250)) = k2_struct_0(A_1250)
      | ~ v1_tops_1('#skF_1'(A_1250),A_1250)
      | ~ l1_pre_topc(A_1250) ) ),
    inference(resolution,[status(thm)],[c_32902,c_299])).

tff(c_32998,plain,(
    ! [A_1251] :
      ( k2_pre_topc(A_1251,u1_struct_0(A_1251)) = k2_struct_0(A_1251)
      | ~ l1_pre_topc(A_1251) ) ),
    inference(resolution,[status(thm)],[c_22,c_32960])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(A_6,k1_zfmisc_1(B_7))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_131,plain,(
    ! [B_85,A_86] :
      ( r1_tarski(B_85,k2_pre_topc(A_86,B_85))
      | ~ m1_subset_1(B_85,k1_zfmisc_1(u1_struct_0(A_86)))
      | ~ l1_pre_topc(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_145,plain,(
    ! [A_6,A_86] :
      ( r1_tarski(A_6,k2_pre_topc(A_86,A_6))
      | ~ l1_pre_topc(A_86)
      | ~ r1_tarski(A_6,u1_struct_0(A_86)) ) ),
    inference(resolution,[status(thm)],[c_10,c_131])).

tff(c_33270,plain,(
    ! [A_1251] :
      ( r1_tarski(u1_struct_0(A_1251),k2_struct_0(A_1251))
      | ~ l1_pre_topc(A_1251)
      | ~ r1_tarski(u1_struct_0(A_1251),u1_struct_0(A_1251))
      | ~ l1_pre_topc(A_1251) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32998,c_145])).

tff(c_33751,plain,(
    ! [A_1253] :
      ( r1_tarski(u1_struct_0(A_1253),k2_struct_0(A_1253))
      | ~ l1_pre_topc(A_1253) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_33270])).

tff(c_543,plain,(
    ! [C_116,A_117,B_118] :
      ( m1_subset_1(C_116,k1_zfmisc_1(u1_struct_0(A_117)))
      | ~ m1_subset_1(C_116,k1_zfmisc_1(u1_struct_0(B_118)))
      | ~ m1_pre_topc(B_118,A_117)
      | ~ l1_pre_topc(A_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1437,plain,(
    ! [A_191,A_192,B_193] :
      ( m1_subset_1(A_191,k1_zfmisc_1(u1_struct_0(A_192)))
      | ~ m1_pre_topc(B_193,A_192)
      | ~ l1_pre_topc(A_192)
      | ~ r1_tarski(A_191,u1_struct_0(B_193)) ) ),
    inference(resolution,[status(thm)],[c_10,c_543])).

tff(c_1439,plain,(
    ! [A_191] :
      ( m1_subset_1(A_191,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ r1_tarski(A_191,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_42,c_1437])).

tff(c_1443,plain,(
    ! [A_194] :
      ( m1_subset_1(A_194,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ r1_tarski(A_194,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_1439])).

tff(c_1474,plain,(
    ! [A_194] :
      ( r1_tarski(A_194,u1_struct_0('#skF_3'))
      | ~ r1_tarski(A_194,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_1443,c_8])).

tff(c_1503,plain,(
    ! [D_196,B_197,A_198] :
      ( v2_compts_1(D_196,B_197)
      | ~ m1_subset_1(D_196,k1_zfmisc_1(u1_struct_0(B_197)))
      | ~ v2_compts_1(D_196,A_198)
      | ~ r1_tarski(D_196,k2_struct_0(B_197))
      | ~ m1_subset_1(D_196,k1_zfmisc_1(u1_struct_0(A_198)))
      | ~ m1_pre_topc(B_197,A_198)
      | ~ l1_pre_topc(A_198) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_17114,plain,(
    ! [A_716,B_717,A_718] :
      ( v2_compts_1(A_716,B_717)
      | ~ v2_compts_1(A_716,A_718)
      | ~ r1_tarski(A_716,k2_struct_0(B_717))
      | ~ m1_subset_1(A_716,k1_zfmisc_1(u1_struct_0(A_718)))
      | ~ m1_pre_topc(B_717,A_718)
      | ~ l1_pre_topc(A_718)
      | ~ r1_tarski(A_716,u1_struct_0(B_717)) ) ),
    inference(resolution,[status(thm)],[c_10,c_1503])).

tff(c_23713,plain,(
    ! [A_950,B_951,A_952] :
      ( v2_compts_1(A_950,B_951)
      | ~ v2_compts_1(A_950,A_952)
      | ~ r1_tarski(A_950,k2_struct_0(B_951))
      | ~ m1_pre_topc(B_951,A_952)
      | ~ l1_pre_topc(A_952)
      | ~ r1_tarski(A_950,u1_struct_0(B_951))
      | ~ r1_tarski(A_950,u1_struct_0(A_952)) ) ),
    inference(resolution,[status(thm)],[c_10,c_17114])).

tff(c_23715,plain,(
    ! [A_950] :
      ( v2_compts_1(A_950,'#skF_4')
      | ~ v2_compts_1(A_950,'#skF_3')
      | ~ r1_tarski(A_950,k2_struct_0('#skF_4'))
      | ~ l1_pre_topc('#skF_3')
      | ~ r1_tarski(A_950,u1_struct_0('#skF_4'))
      | ~ r1_tarski(A_950,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_42,c_23713])).

tff(c_24597,plain,(
    ! [A_963] :
      ( v2_compts_1(A_963,'#skF_4')
      | ~ v2_compts_1(A_963,'#skF_3')
      | ~ r1_tarski(A_963,k2_struct_0('#skF_4'))
      | ~ r1_tarski(A_963,u1_struct_0('#skF_4'))
      | ~ r1_tarski(A_963,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_23715])).

tff(c_25332,plain,(
    ! [A_981] :
      ( v2_compts_1(A_981,'#skF_4')
      | ~ v2_compts_1(A_981,'#skF_3')
      | ~ r1_tarski(A_981,k2_struct_0('#skF_4'))
      | ~ r1_tarski(A_981,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_1474,c_24597])).

tff(c_25443,plain,
    ( v2_compts_1(u1_struct_0('#skF_4'),'#skF_4')
    | ~ v2_compts_1(u1_struct_0('#skF_4'),'#skF_3')
    | ~ r1_tarski(u1_struct_0('#skF_4'),k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_98,c_25332])).

tff(c_26036,plain,(
    ~ r1_tarski(u1_struct_0('#skF_4'),k2_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_25443])).

tff(c_33774,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_33751,c_26036])).

tff(c_33860,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_33774])).

tff(c_33862,plain,(
    r1_tarski(u1_struct_0('#skF_4'),k2_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_25443])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(B_2,C_3)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_33955,plain,(
    ! [A_1258] :
      ( r1_tarski(A_1258,k2_struct_0('#skF_4'))
      | ~ r1_tarski(A_1258,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_33862,c_2])).

tff(c_34064,plain,(
    r1_tarski('#skF_6',k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_96,c_33955])).

tff(c_1442,plain,(
    ! [A_191] :
      ( m1_subset_1(A_191,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ r1_tarski(A_191,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_1439])).

tff(c_32,plain,(
    ! [A_33,B_45,C_51] :
      ( '#skF_2'(A_33,B_45,C_51) = C_51
      | v2_compts_1(C_51,A_33)
      | ~ r1_tarski(C_51,k2_struct_0(B_45))
      | ~ m1_subset_1(C_51,k1_zfmisc_1(u1_struct_0(A_33)))
      | ~ m1_pre_topc(B_45,A_33)
      | ~ l1_pre_topc(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_67330,plain,(
    ! [A_1888] :
      ( '#skF_2'(A_1888,'#skF_4','#skF_6') = '#skF_6'
      | v2_compts_1('#skF_6',A_1888)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0(A_1888)))
      | ~ m1_pre_topc('#skF_4',A_1888)
      | ~ l1_pre_topc(A_1888) ) ),
    inference(resolution,[status(thm)],[c_34064,c_32])).

tff(c_67338,plain,
    ( '#skF_2'('#skF_3','#skF_4','#skF_6') = '#skF_6'
    | v2_compts_1('#skF_6','#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ r1_tarski('#skF_6',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_1442,c_67330])).

tff(c_67359,plain,
    ( '#skF_2'('#skF_3','#skF_4','#skF_6') = '#skF_6'
    | v2_compts_1('#skF_6','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_44,c_42,c_67338])).

tff(c_67360,plain,(
    '#skF_2'('#skF_3','#skF_4','#skF_6') = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_73,c_67359])).

tff(c_30,plain,(
    ! [A_33,B_45,C_51] :
      ( ~ v2_compts_1('#skF_2'(A_33,B_45,C_51),B_45)
      | v2_compts_1(C_51,A_33)
      | ~ r1_tarski(C_51,k2_struct_0(B_45))
      | ~ m1_subset_1(C_51,k1_zfmisc_1(u1_struct_0(A_33)))
      | ~ m1_pre_topc(B_45,A_33)
      | ~ l1_pre_topc(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_67442,plain,
    ( ~ v2_compts_1('#skF_6','#skF_4')
    | v2_compts_1('#skF_6','#skF_3')
    | ~ r1_tarski('#skF_6',k2_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_67360,c_30])).

tff(c_67520,plain,(
    v2_compts_1('#skF_6','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_54,c_34064,c_72,c_67442])).

tff(c_67522,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_73,c_67520])).

tff(c_67523,plain,(
    ~ v2_compts_1('#skF_6','#skF_4') ),
    inference(splitRight,[status(thm)],[c_53])).

tff(c_67526,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_67523])).

tff(c_67527,plain,(
    v2_compts_1('#skF_6','#skF_3') ),
    inference(splitRight,[status(thm)],[c_55])).

tff(c_67689,plain,(
    ! [C_1913,A_1914,B_1915] :
      ( m1_subset_1(C_1913,k1_zfmisc_1(u1_struct_0(A_1914)))
      | ~ m1_subset_1(C_1913,k1_zfmisc_1(u1_struct_0(B_1915)))
      | ~ m1_pre_topc(B_1915,A_1914)
      | ~ l1_pre_topc(A_1914) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_68930,plain,(
    ! [A_2014,A_2015,B_2016] :
      ( m1_subset_1(A_2014,k1_zfmisc_1(u1_struct_0(A_2015)))
      | ~ m1_pre_topc(B_2016,A_2015)
      | ~ l1_pre_topc(A_2015)
      | ~ r1_tarski(A_2014,u1_struct_0(B_2016)) ) ),
    inference(resolution,[status(thm)],[c_10,c_67689])).

tff(c_68932,plain,(
    ! [A_2014] :
      ( m1_subset_1(A_2014,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ r1_tarski(A_2014,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_42,c_68930])).

tff(c_68935,plain,(
    ! [A_2014] :
      ( m1_subset_1(A_2014,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ r1_tarski(A_2014,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_68932])).

tff(c_67528,plain,(
    ~ v2_compts_1('#skF_6','#skF_4') ),
    inference(splitRight,[status(thm)],[c_55])).

tff(c_68893,plain,(
    ! [D_2010,B_2011,A_2012] :
      ( v2_compts_1(D_2010,B_2011)
      | ~ m1_subset_1(D_2010,k1_zfmisc_1(u1_struct_0(B_2011)))
      | ~ v2_compts_1(D_2010,A_2012)
      | ~ r1_tarski(D_2010,k2_struct_0(B_2011))
      | ~ m1_subset_1(D_2010,k1_zfmisc_1(u1_struct_0(A_2012)))
      | ~ m1_pre_topc(B_2011,A_2012)
      | ~ l1_pre_topc(A_2012) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_68910,plain,(
    ! [A_2012] :
      ( v2_compts_1('#skF_6','#skF_4')
      | ~ v2_compts_1('#skF_6',A_2012)
      | ~ r1_tarski('#skF_6',k2_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0(A_2012)))
      | ~ m1_pre_topc('#skF_4',A_2012)
      | ~ l1_pre_topc(A_2012) ) ),
    inference(resolution,[status(thm)],[c_38,c_68893])).

tff(c_68925,plain,(
    ! [A_2012] :
      ( ~ v2_compts_1('#skF_6',A_2012)
      | ~ r1_tarski('#skF_6',k2_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0(A_2012)))
      | ~ m1_pre_topc('#skF_4',A_2012)
      | ~ l1_pre_topc(A_2012) ) ),
    inference(negUnitSimplification,[status(thm)],[c_67528,c_68910])).

tff(c_68971,plain,(
    ~ r1_tarski('#skF_6',k2_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_68925])).

tff(c_67550,plain,(
    ! [B_1894,A_1895] :
      ( l1_pre_topc(B_1894)
      | ~ m1_pre_topc(B_1894,A_1895)
      | ~ l1_pre_topc(A_1895) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_67553,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_67550])).

tff(c_67556,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_67553])).

tff(c_67557,plain,(
    ! [A_1896] :
      ( m1_subset_1('#skF_1'(A_1896),k1_zfmisc_1(u1_struct_0(A_1896)))
      | ~ l1_pre_topc(A_1896) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_67561,plain,(
    ! [A_1896] :
      ( r1_tarski('#skF_1'(A_1896),u1_struct_0(A_1896))
      | ~ l1_pre_topc(A_1896) ) ),
    inference(resolution,[status(thm)],[c_67557,c_8])).

tff(c_68124,plain,(
    ! [C_1945,A_1946,B_1947] :
      ( v1_tops_1(C_1945,A_1946)
      | ~ r1_tarski(B_1947,C_1945)
      | ~ v1_tops_1(B_1947,A_1946)
      | ~ m1_subset_1(C_1945,k1_zfmisc_1(u1_struct_0(A_1946)))
      | ~ m1_subset_1(B_1947,k1_zfmisc_1(u1_struct_0(A_1946)))
      | ~ l1_pre_topc(A_1946) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_77506,plain,(
    ! [A_2281,A_2282] :
      ( v1_tops_1(u1_struct_0(A_2281),A_2282)
      | ~ v1_tops_1('#skF_1'(A_2281),A_2282)
      | ~ m1_subset_1(u1_struct_0(A_2281),k1_zfmisc_1(u1_struct_0(A_2282)))
      | ~ m1_subset_1('#skF_1'(A_2281),k1_zfmisc_1(u1_struct_0(A_2282)))
      | ~ l1_pre_topc(A_2282)
      | ~ l1_pre_topc(A_2281) ) ),
    inference(resolution,[status(thm)],[c_67561,c_68124])).

tff(c_84024,plain,(
    ! [A_2543] :
      ( v1_tops_1(u1_struct_0(A_2543),A_2543)
      | ~ v1_tops_1('#skF_1'(A_2543),A_2543)
      | ~ m1_subset_1('#skF_1'(A_2543),k1_zfmisc_1(u1_struct_0(A_2543)))
      | ~ l1_pre_topc(A_2543) ) ),
    inference(resolution,[status(thm)],[c_56,c_77506])).

tff(c_84062,plain,(
    ! [A_2544] :
      ( v1_tops_1(u1_struct_0(A_2544),A_2544)
      | ~ v1_tops_1('#skF_1'(A_2544),A_2544)
      | ~ l1_pre_topc(A_2544) ) ),
    inference(resolution,[status(thm)],[c_24,c_84024])).

tff(c_67804,plain,(
    ! [A_1924,B_1925] :
      ( k2_pre_topc(A_1924,B_1925) = k2_struct_0(A_1924)
      | ~ v1_tops_1(B_1925,A_1924)
      | ~ m1_subset_1(B_1925,k1_zfmisc_1(u1_struct_0(A_1924)))
      | ~ l1_pre_topc(A_1924) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_67838,plain,(
    ! [A_1924] :
      ( k2_pre_topc(A_1924,u1_struct_0(A_1924)) = k2_struct_0(A_1924)
      | ~ v1_tops_1(u1_struct_0(A_1924),A_1924)
      | ~ l1_pre_topc(A_1924) ) ),
    inference(resolution,[status(thm)],[c_56,c_67804])).

tff(c_84099,plain,(
    ! [A_2545] :
      ( k2_pre_topc(A_2545,u1_struct_0(A_2545)) = k2_struct_0(A_2545)
      | ~ v1_tops_1('#skF_1'(A_2545),A_2545)
      | ~ l1_pre_topc(A_2545) ) ),
    inference(resolution,[status(thm)],[c_84062,c_67838])).

tff(c_84138,plain,(
    ! [A_2547] :
      ( k2_pre_topc(A_2547,u1_struct_0(A_2547)) = k2_struct_0(A_2547)
      | ~ l1_pre_topc(A_2547) ) ),
    inference(resolution,[status(thm)],[c_22,c_84099])).

tff(c_67548,plain,(
    ! [A_5] : r1_tarski(A_5,A_5) ),
    inference(resolution,[status(thm)],[c_56,c_67532])).

tff(c_67656,plain,(
    ! [B_1911,A_1912] :
      ( r1_tarski(B_1911,k2_pre_topc(A_1912,B_1911))
      | ~ m1_subset_1(B_1911,k1_zfmisc_1(u1_struct_0(A_1912)))
      | ~ l1_pre_topc(A_1912) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_67759,plain,(
    ! [A_1920] :
      ( r1_tarski(u1_struct_0(A_1920),k2_pre_topc(A_1920,u1_struct_0(A_1920)))
      | ~ l1_pre_topc(A_1920) ) ),
    inference(resolution,[status(thm)],[c_56,c_67656])).

tff(c_68269,plain,(
    ! [A_1954,A_1955] :
      ( r1_tarski(A_1954,k2_pre_topc(A_1955,u1_struct_0(A_1955)))
      | ~ r1_tarski(A_1954,u1_struct_0(A_1955))
      | ~ l1_pre_topc(A_1955) ) ),
    inference(resolution,[status(thm)],[c_67759,c_2])).

tff(c_75371,plain,(
    ! [A_2248,A_2249,A_2250] :
      ( r1_tarski(A_2248,k2_pre_topc(A_2249,u1_struct_0(A_2249)))
      | ~ r1_tarski(A_2248,A_2250)
      | ~ r1_tarski(A_2250,u1_struct_0(A_2249))
      | ~ l1_pre_topc(A_2249) ) ),
    inference(resolution,[status(thm)],[c_68269,c_2])).

tff(c_75585,plain,(
    ! [A_2251] :
      ( r1_tarski('#skF_6',k2_pre_topc(A_2251,u1_struct_0(A_2251)))
      | ~ r1_tarski(u1_struct_0('#skF_4'),u1_struct_0(A_2251))
      | ~ l1_pre_topc(A_2251) ) ),
    inference(resolution,[status(thm)],[c_67546,c_75371])).

tff(c_75623,plain,
    ( r1_tarski('#skF_6',k2_pre_topc('#skF_4',u1_struct_0('#skF_4')))
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_67548,c_75585])).

tff(c_75648,plain,(
    r1_tarski('#skF_6',k2_pre_topc('#skF_4',u1_struct_0('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_67556,c_75623])).

tff(c_84312,plain,
    ( r1_tarski('#skF_6',k2_struct_0('#skF_4'))
    | ~ l1_pre_topc('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_84138,c_75648])).

tff(c_84493,plain,(
    r1_tarski('#skF_6',k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_67556,c_84312])).

tff(c_84495,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68971,c_84493])).

tff(c_84616,plain,(
    ! [A_2551] :
      ( ~ v2_compts_1('#skF_6',A_2551)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0(A_2551)))
      | ~ m1_pre_topc('#skF_4',A_2551)
      | ~ l1_pre_topc(A_2551) ) ),
    inference(splitRight,[status(thm)],[c_68925])).

tff(c_84620,plain,
    ( ~ v2_compts_1('#skF_6','#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ r1_tarski('#skF_6',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_68935,c_84616])).

tff(c_84639,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_67546,c_44,c_42,c_67527,c_84620])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:55:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 25.35/16.23  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 25.39/16.24  
% 25.39/16.24  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 25.39/16.24  %$ v2_compts_1 > v1_tops_1 > r1_tarski > m1_subset_1 > m1_pre_topc > l1_pre_topc > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4
% 25.39/16.24  
% 25.39/16.24  %Foreground sorts:
% 25.39/16.24  
% 25.39/16.24  
% 25.39/16.24  %Background operators:
% 25.39/16.24  
% 25.39/16.24  
% 25.39/16.24  %Foreground operators:
% 25.39/16.24  tff(v2_compts_1, type, v2_compts_1: ($i * $i) > $o).
% 25.39/16.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 25.39/16.24  tff('#skF_1', type, '#skF_1': $i > $i).
% 25.39/16.24  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 25.39/16.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 25.39/16.24  tff('#skF_5', type, '#skF_5': $i).
% 25.39/16.24  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 25.39/16.24  tff('#skF_6', type, '#skF_6': $i).
% 25.39/16.24  tff('#skF_3', type, '#skF_3': $i).
% 25.39/16.24  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 25.39/16.24  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 25.39/16.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 25.39/16.24  tff('#skF_4', type, '#skF_4': $i).
% 25.39/16.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 25.39/16.24  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 25.39/16.24  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 25.39/16.24  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 25.39/16.24  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 25.39/16.24  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 25.39/16.24  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 25.39/16.24  
% 25.39/16.27  tff(f_130, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => ((C = D) => (v2_compts_1(C, A) <=> v2_compts_1(D, B))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_compts_1)).
% 25.39/16.27  tff(f_39, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 25.39/16.27  tff(f_46, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 25.39/16.27  tff(f_33, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 25.39/16.27  tff(f_35, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 25.39/16.27  tff(f_79, axiom, (![A]: (l1_pre_topc(A) => (?[B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) & v1_tops_1(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc4_tops_1)).
% 25.39/16.27  tff(f_93, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v1_tops_1(B, A) & r1_tarski(B, C)) => v1_tops_1(C, A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_tops_1)).
% 25.39/16.27  tff(f_72, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = k2_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tops_1)).
% 25.39/16.27  tff(f_63, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(B, k2_pre_topc(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_pre_topc)).
% 25.39/16.27  tff(f_56, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B))) => m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_pre_topc)).
% 25.39/16.27  tff(f_112, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(C, k2_struct_0(B)) => (v2_compts_1(C, A) <=> (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => ((D = C) => v2_compts_1(D, B)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_compts_1)).
% 25.39/16.27  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 25.39/16.27  tff(c_38, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_130])).
% 25.39/16.27  tff(c_67532, plain, (![A_1891, B_1892]: (r1_tarski(A_1891, B_1892) | ~m1_subset_1(A_1891, k1_zfmisc_1(B_1892)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 25.39/16.27  tff(c_67546, plain, (r1_tarski('#skF_6', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_38, c_67532])).
% 25.39/16.27  tff(c_44, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_130])).
% 25.39/16.27  tff(c_42, plain, (m1_pre_topc('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_130])).
% 25.39/16.27  tff(c_36, plain, ('#skF_5'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_130])).
% 25.39/16.27  tff(c_52, plain, (v2_compts_1('#skF_5', '#skF_3') | v2_compts_1('#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_130])).
% 25.39/16.27  tff(c_55, plain, (v2_compts_1('#skF_6', '#skF_3') | v2_compts_1('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_52])).
% 25.39/16.27  tff(c_72, plain, (v2_compts_1('#skF_6', '#skF_4')), inference(splitLeft, [status(thm)], [c_55])).
% 25.39/16.27  tff(c_46, plain, (~v2_compts_1('#skF_6', '#skF_4') | ~v2_compts_1('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_130])).
% 25.39/16.27  tff(c_53, plain, (~v2_compts_1('#skF_6', '#skF_4') | ~v2_compts_1('#skF_6', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_46])).
% 25.39/16.27  tff(c_73, plain, (~v2_compts_1('#skF_6', '#skF_3')), inference(splitLeft, [status(thm)], [c_53])).
% 25.39/16.27  tff(c_40, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_130])).
% 25.39/16.27  tff(c_54, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_40])).
% 25.39/16.27  tff(c_82, plain, (![A_73, B_74]: (r1_tarski(A_73, B_74) | ~m1_subset_1(A_73, k1_zfmisc_1(B_74)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 25.39/16.27  tff(c_96, plain, (r1_tarski('#skF_6', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_38, c_82])).
% 25.39/16.27  tff(c_74, plain, (![B_69, A_70]: (l1_pre_topc(B_69) | ~m1_pre_topc(B_69, A_70) | ~l1_pre_topc(A_70))), inference(cnfTransformation, [status(thm)], [f_46])).
% 25.39/16.27  tff(c_77, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_42, c_74])).
% 25.39/16.27  tff(c_80, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_77])).
% 25.39/16.27  tff(c_4, plain, (![A_4]: (k2_subset_1(A_4)=A_4)), inference(cnfTransformation, [status(thm)], [f_33])).
% 25.39/16.27  tff(c_6, plain, (![A_5]: (m1_subset_1(k2_subset_1(A_5), k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 25.39/16.27  tff(c_56, plain, (![A_5]: (m1_subset_1(A_5, k1_zfmisc_1(A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_6])).
% 25.39/16.27  tff(c_98, plain, (![A_5]: (r1_tarski(A_5, A_5))), inference(resolution, [status(thm)], [c_56, c_82])).
% 25.39/16.27  tff(c_22, plain, (![A_24]: (v1_tops_1('#skF_1'(A_24), A_24) | ~l1_pre_topc(A_24))), inference(cnfTransformation, [status(thm)], [f_79])).
% 25.39/16.27  tff(c_24, plain, (![A_24]: (m1_subset_1('#skF_1'(A_24), k1_zfmisc_1(u1_struct_0(A_24))) | ~l1_pre_topc(A_24))), inference(cnfTransformation, [status(thm)], [f_79])).
% 25.39/16.27  tff(c_100, plain, (![A_76]: (m1_subset_1('#skF_1'(A_76), k1_zfmisc_1(u1_struct_0(A_76))) | ~l1_pre_topc(A_76))), inference(cnfTransformation, [status(thm)], [f_79])).
% 25.39/16.27  tff(c_8, plain, (![A_6, B_7]: (r1_tarski(A_6, B_7) | ~m1_subset_1(A_6, k1_zfmisc_1(B_7)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 25.39/16.27  tff(c_104, plain, (![A_76]: (r1_tarski('#skF_1'(A_76), u1_struct_0(A_76)) | ~l1_pre_topc(A_76))), inference(resolution, [status(thm)], [c_100, c_8])).
% 25.39/16.27  tff(c_719, plain, (![C_130, A_131, B_132]: (v1_tops_1(C_130, A_131) | ~r1_tarski(B_132, C_130) | ~v1_tops_1(B_132, A_131) | ~m1_subset_1(C_130, k1_zfmisc_1(u1_struct_0(A_131))) | ~m1_subset_1(B_132, k1_zfmisc_1(u1_struct_0(A_131))) | ~l1_pre_topc(A_131))), inference(cnfTransformation, [status(thm)], [f_93])).
% 25.39/16.27  tff(c_25122, plain, (![A_976, A_977]: (v1_tops_1(u1_struct_0(A_976), A_977) | ~v1_tops_1('#skF_1'(A_976), A_977) | ~m1_subset_1(u1_struct_0(A_976), k1_zfmisc_1(u1_struct_0(A_977))) | ~m1_subset_1('#skF_1'(A_976), k1_zfmisc_1(u1_struct_0(A_977))) | ~l1_pre_topc(A_977) | ~l1_pre_topc(A_976))), inference(resolution, [status(thm)], [c_104, c_719])).
% 25.39/16.27  tff(c_32864, plain, (![A_1245]: (v1_tops_1(u1_struct_0(A_1245), A_1245) | ~v1_tops_1('#skF_1'(A_1245), A_1245) | ~m1_subset_1('#skF_1'(A_1245), k1_zfmisc_1(u1_struct_0(A_1245))) | ~l1_pre_topc(A_1245))), inference(resolution, [status(thm)], [c_56, c_25122])).
% 25.39/16.27  tff(c_32902, plain, (![A_1246]: (v1_tops_1(u1_struct_0(A_1246), A_1246) | ~v1_tops_1('#skF_1'(A_1246), A_1246) | ~l1_pre_topc(A_1246))), inference(resolution, [status(thm)], [c_24, c_32864])).
% 25.39/16.27  tff(c_273, plain, (![A_97, B_98]: (k2_pre_topc(A_97, B_98)=k2_struct_0(A_97) | ~v1_tops_1(B_98, A_97) | ~m1_subset_1(B_98, k1_zfmisc_1(u1_struct_0(A_97))) | ~l1_pre_topc(A_97))), inference(cnfTransformation, [status(thm)], [f_72])).
% 25.39/16.27  tff(c_299, plain, (![A_97]: (k2_pre_topc(A_97, u1_struct_0(A_97))=k2_struct_0(A_97) | ~v1_tops_1(u1_struct_0(A_97), A_97) | ~l1_pre_topc(A_97))), inference(resolution, [status(thm)], [c_56, c_273])).
% 25.39/16.27  tff(c_32960, plain, (![A_1250]: (k2_pre_topc(A_1250, u1_struct_0(A_1250))=k2_struct_0(A_1250) | ~v1_tops_1('#skF_1'(A_1250), A_1250) | ~l1_pre_topc(A_1250))), inference(resolution, [status(thm)], [c_32902, c_299])).
% 25.39/16.27  tff(c_32998, plain, (![A_1251]: (k2_pre_topc(A_1251, u1_struct_0(A_1251))=k2_struct_0(A_1251) | ~l1_pre_topc(A_1251))), inference(resolution, [status(thm)], [c_22, c_32960])).
% 25.39/16.27  tff(c_10, plain, (![A_6, B_7]: (m1_subset_1(A_6, k1_zfmisc_1(B_7)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 25.39/16.27  tff(c_131, plain, (![B_85, A_86]: (r1_tarski(B_85, k2_pre_topc(A_86, B_85)) | ~m1_subset_1(B_85, k1_zfmisc_1(u1_struct_0(A_86))) | ~l1_pre_topc(A_86))), inference(cnfTransformation, [status(thm)], [f_63])).
% 25.39/16.27  tff(c_145, plain, (![A_6, A_86]: (r1_tarski(A_6, k2_pre_topc(A_86, A_6)) | ~l1_pre_topc(A_86) | ~r1_tarski(A_6, u1_struct_0(A_86)))), inference(resolution, [status(thm)], [c_10, c_131])).
% 25.39/16.27  tff(c_33270, plain, (![A_1251]: (r1_tarski(u1_struct_0(A_1251), k2_struct_0(A_1251)) | ~l1_pre_topc(A_1251) | ~r1_tarski(u1_struct_0(A_1251), u1_struct_0(A_1251)) | ~l1_pre_topc(A_1251))), inference(superposition, [status(thm), theory('equality')], [c_32998, c_145])).
% 25.39/16.27  tff(c_33751, plain, (![A_1253]: (r1_tarski(u1_struct_0(A_1253), k2_struct_0(A_1253)) | ~l1_pre_topc(A_1253))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_33270])).
% 25.39/16.27  tff(c_543, plain, (![C_116, A_117, B_118]: (m1_subset_1(C_116, k1_zfmisc_1(u1_struct_0(A_117))) | ~m1_subset_1(C_116, k1_zfmisc_1(u1_struct_0(B_118))) | ~m1_pre_topc(B_118, A_117) | ~l1_pre_topc(A_117))), inference(cnfTransformation, [status(thm)], [f_56])).
% 25.39/16.27  tff(c_1437, plain, (![A_191, A_192, B_193]: (m1_subset_1(A_191, k1_zfmisc_1(u1_struct_0(A_192))) | ~m1_pre_topc(B_193, A_192) | ~l1_pre_topc(A_192) | ~r1_tarski(A_191, u1_struct_0(B_193)))), inference(resolution, [status(thm)], [c_10, c_543])).
% 25.39/16.27  tff(c_1439, plain, (![A_191]: (m1_subset_1(A_191, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~r1_tarski(A_191, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_42, c_1437])).
% 25.39/16.27  tff(c_1443, plain, (![A_194]: (m1_subset_1(A_194, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~r1_tarski(A_194, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_1439])).
% 25.39/16.27  tff(c_1474, plain, (![A_194]: (r1_tarski(A_194, u1_struct_0('#skF_3')) | ~r1_tarski(A_194, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_1443, c_8])).
% 25.39/16.27  tff(c_1503, plain, (![D_196, B_197, A_198]: (v2_compts_1(D_196, B_197) | ~m1_subset_1(D_196, k1_zfmisc_1(u1_struct_0(B_197))) | ~v2_compts_1(D_196, A_198) | ~r1_tarski(D_196, k2_struct_0(B_197)) | ~m1_subset_1(D_196, k1_zfmisc_1(u1_struct_0(A_198))) | ~m1_pre_topc(B_197, A_198) | ~l1_pre_topc(A_198))), inference(cnfTransformation, [status(thm)], [f_112])).
% 25.39/16.27  tff(c_17114, plain, (![A_716, B_717, A_718]: (v2_compts_1(A_716, B_717) | ~v2_compts_1(A_716, A_718) | ~r1_tarski(A_716, k2_struct_0(B_717)) | ~m1_subset_1(A_716, k1_zfmisc_1(u1_struct_0(A_718))) | ~m1_pre_topc(B_717, A_718) | ~l1_pre_topc(A_718) | ~r1_tarski(A_716, u1_struct_0(B_717)))), inference(resolution, [status(thm)], [c_10, c_1503])).
% 25.39/16.27  tff(c_23713, plain, (![A_950, B_951, A_952]: (v2_compts_1(A_950, B_951) | ~v2_compts_1(A_950, A_952) | ~r1_tarski(A_950, k2_struct_0(B_951)) | ~m1_pre_topc(B_951, A_952) | ~l1_pre_topc(A_952) | ~r1_tarski(A_950, u1_struct_0(B_951)) | ~r1_tarski(A_950, u1_struct_0(A_952)))), inference(resolution, [status(thm)], [c_10, c_17114])).
% 25.39/16.27  tff(c_23715, plain, (![A_950]: (v2_compts_1(A_950, '#skF_4') | ~v2_compts_1(A_950, '#skF_3') | ~r1_tarski(A_950, k2_struct_0('#skF_4')) | ~l1_pre_topc('#skF_3') | ~r1_tarski(A_950, u1_struct_0('#skF_4')) | ~r1_tarski(A_950, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_42, c_23713])).
% 25.39/16.27  tff(c_24597, plain, (![A_963]: (v2_compts_1(A_963, '#skF_4') | ~v2_compts_1(A_963, '#skF_3') | ~r1_tarski(A_963, k2_struct_0('#skF_4')) | ~r1_tarski(A_963, u1_struct_0('#skF_4')) | ~r1_tarski(A_963, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_23715])).
% 25.39/16.27  tff(c_25332, plain, (![A_981]: (v2_compts_1(A_981, '#skF_4') | ~v2_compts_1(A_981, '#skF_3') | ~r1_tarski(A_981, k2_struct_0('#skF_4')) | ~r1_tarski(A_981, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_1474, c_24597])).
% 25.39/16.27  tff(c_25443, plain, (v2_compts_1(u1_struct_0('#skF_4'), '#skF_4') | ~v2_compts_1(u1_struct_0('#skF_4'), '#skF_3') | ~r1_tarski(u1_struct_0('#skF_4'), k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_98, c_25332])).
% 25.39/16.27  tff(c_26036, plain, (~r1_tarski(u1_struct_0('#skF_4'), k2_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_25443])).
% 25.39/16.27  tff(c_33774, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_33751, c_26036])).
% 25.39/16.27  tff(c_33860, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_80, c_33774])).
% 25.39/16.27  tff(c_33862, plain, (r1_tarski(u1_struct_0('#skF_4'), k2_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_25443])).
% 25.39/16.27  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(B_2, C_3) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 25.39/16.27  tff(c_33955, plain, (![A_1258]: (r1_tarski(A_1258, k2_struct_0('#skF_4')) | ~r1_tarski(A_1258, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_33862, c_2])).
% 25.39/16.27  tff(c_34064, plain, (r1_tarski('#skF_6', k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_96, c_33955])).
% 25.39/16.27  tff(c_1442, plain, (![A_191]: (m1_subset_1(A_191, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~r1_tarski(A_191, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_1439])).
% 25.39/16.27  tff(c_32, plain, (![A_33, B_45, C_51]: ('#skF_2'(A_33, B_45, C_51)=C_51 | v2_compts_1(C_51, A_33) | ~r1_tarski(C_51, k2_struct_0(B_45)) | ~m1_subset_1(C_51, k1_zfmisc_1(u1_struct_0(A_33))) | ~m1_pre_topc(B_45, A_33) | ~l1_pre_topc(A_33))), inference(cnfTransformation, [status(thm)], [f_112])).
% 25.39/16.27  tff(c_67330, plain, (![A_1888]: ('#skF_2'(A_1888, '#skF_4', '#skF_6')='#skF_6' | v2_compts_1('#skF_6', A_1888) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0(A_1888))) | ~m1_pre_topc('#skF_4', A_1888) | ~l1_pre_topc(A_1888))), inference(resolution, [status(thm)], [c_34064, c_32])).
% 25.39/16.27  tff(c_67338, plain, ('#skF_2'('#skF_3', '#skF_4', '#skF_6')='#skF_6' | v2_compts_1('#skF_6', '#skF_3') | ~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~r1_tarski('#skF_6', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_1442, c_67330])).
% 25.39/16.27  tff(c_67359, plain, ('#skF_2'('#skF_3', '#skF_4', '#skF_6')='#skF_6' | v2_compts_1('#skF_6', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_96, c_44, c_42, c_67338])).
% 25.39/16.27  tff(c_67360, plain, ('#skF_2'('#skF_3', '#skF_4', '#skF_6')='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_73, c_67359])).
% 25.39/16.27  tff(c_30, plain, (![A_33, B_45, C_51]: (~v2_compts_1('#skF_2'(A_33, B_45, C_51), B_45) | v2_compts_1(C_51, A_33) | ~r1_tarski(C_51, k2_struct_0(B_45)) | ~m1_subset_1(C_51, k1_zfmisc_1(u1_struct_0(A_33))) | ~m1_pre_topc(B_45, A_33) | ~l1_pre_topc(A_33))), inference(cnfTransformation, [status(thm)], [f_112])).
% 25.39/16.27  tff(c_67442, plain, (~v2_compts_1('#skF_6', '#skF_4') | v2_compts_1('#skF_6', '#skF_3') | ~r1_tarski('#skF_6', k2_struct_0('#skF_4')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_67360, c_30])).
% 25.39/16.27  tff(c_67520, plain, (v2_compts_1('#skF_6', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_54, c_34064, c_72, c_67442])).
% 25.39/16.27  tff(c_67522, plain, $false, inference(negUnitSimplification, [status(thm)], [c_73, c_67520])).
% 25.39/16.27  tff(c_67523, plain, (~v2_compts_1('#skF_6', '#skF_4')), inference(splitRight, [status(thm)], [c_53])).
% 25.39/16.27  tff(c_67526, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72, c_67523])).
% 25.39/16.27  tff(c_67527, plain, (v2_compts_1('#skF_6', '#skF_3')), inference(splitRight, [status(thm)], [c_55])).
% 25.39/16.27  tff(c_67689, plain, (![C_1913, A_1914, B_1915]: (m1_subset_1(C_1913, k1_zfmisc_1(u1_struct_0(A_1914))) | ~m1_subset_1(C_1913, k1_zfmisc_1(u1_struct_0(B_1915))) | ~m1_pre_topc(B_1915, A_1914) | ~l1_pre_topc(A_1914))), inference(cnfTransformation, [status(thm)], [f_56])).
% 25.39/16.27  tff(c_68930, plain, (![A_2014, A_2015, B_2016]: (m1_subset_1(A_2014, k1_zfmisc_1(u1_struct_0(A_2015))) | ~m1_pre_topc(B_2016, A_2015) | ~l1_pre_topc(A_2015) | ~r1_tarski(A_2014, u1_struct_0(B_2016)))), inference(resolution, [status(thm)], [c_10, c_67689])).
% 25.39/16.27  tff(c_68932, plain, (![A_2014]: (m1_subset_1(A_2014, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~r1_tarski(A_2014, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_42, c_68930])).
% 25.39/16.27  tff(c_68935, plain, (![A_2014]: (m1_subset_1(A_2014, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~r1_tarski(A_2014, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_68932])).
% 25.39/16.27  tff(c_67528, plain, (~v2_compts_1('#skF_6', '#skF_4')), inference(splitRight, [status(thm)], [c_55])).
% 25.39/16.27  tff(c_68893, plain, (![D_2010, B_2011, A_2012]: (v2_compts_1(D_2010, B_2011) | ~m1_subset_1(D_2010, k1_zfmisc_1(u1_struct_0(B_2011))) | ~v2_compts_1(D_2010, A_2012) | ~r1_tarski(D_2010, k2_struct_0(B_2011)) | ~m1_subset_1(D_2010, k1_zfmisc_1(u1_struct_0(A_2012))) | ~m1_pre_topc(B_2011, A_2012) | ~l1_pre_topc(A_2012))), inference(cnfTransformation, [status(thm)], [f_112])).
% 25.39/16.27  tff(c_68910, plain, (![A_2012]: (v2_compts_1('#skF_6', '#skF_4') | ~v2_compts_1('#skF_6', A_2012) | ~r1_tarski('#skF_6', k2_struct_0('#skF_4')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0(A_2012))) | ~m1_pre_topc('#skF_4', A_2012) | ~l1_pre_topc(A_2012))), inference(resolution, [status(thm)], [c_38, c_68893])).
% 25.39/16.27  tff(c_68925, plain, (![A_2012]: (~v2_compts_1('#skF_6', A_2012) | ~r1_tarski('#skF_6', k2_struct_0('#skF_4')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0(A_2012))) | ~m1_pre_topc('#skF_4', A_2012) | ~l1_pre_topc(A_2012))), inference(negUnitSimplification, [status(thm)], [c_67528, c_68910])).
% 25.39/16.27  tff(c_68971, plain, (~r1_tarski('#skF_6', k2_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_68925])).
% 25.39/16.27  tff(c_67550, plain, (![B_1894, A_1895]: (l1_pre_topc(B_1894) | ~m1_pre_topc(B_1894, A_1895) | ~l1_pre_topc(A_1895))), inference(cnfTransformation, [status(thm)], [f_46])).
% 25.39/16.27  tff(c_67553, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_42, c_67550])).
% 25.39/16.27  tff(c_67556, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_67553])).
% 25.39/16.27  tff(c_67557, plain, (![A_1896]: (m1_subset_1('#skF_1'(A_1896), k1_zfmisc_1(u1_struct_0(A_1896))) | ~l1_pre_topc(A_1896))), inference(cnfTransformation, [status(thm)], [f_79])).
% 25.39/16.27  tff(c_67561, plain, (![A_1896]: (r1_tarski('#skF_1'(A_1896), u1_struct_0(A_1896)) | ~l1_pre_topc(A_1896))), inference(resolution, [status(thm)], [c_67557, c_8])).
% 25.39/16.27  tff(c_68124, plain, (![C_1945, A_1946, B_1947]: (v1_tops_1(C_1945, A_1946) | ~r1_tarski(B_1947, C_1945) | ~v1_tops_1(B_1947, A_1946) | ~m1_subset_1(C_1945, k1_zfmisc_1(u1_struct_0(A_1946))) | ~m1_subset_1(B_1947, k1_zfmisc_1(u1_struct_0(A_1946))) | ~l1_pre_topc(A_1946))), inference(cnfTransformation, [status(thm)], [f_93])).
% 25.39/16.27  tff(c_77506, plain, (![A_2281, A_2282]: (v1_tops_1(u1_struct_0(A_2281), A_2282) | ~v1_tops_1('#skF_1'(A_2281), A_2282) | ~m1_subset_1(u1_struct_0(A_2281), k1_zfmisc_1(u1_struct_0(A_2282))) | ~m1_subset_1('#skF_1'(A_2281), k1_zfmisc_1(u1_struct_0(A_2282))) | ~l1_pre_topc(A_2282) | ~l1_pre_topc(A_2281))), inference(resolution, [status(thm)], [c_67561, c_68124])).
% 25.39/16.27  tff(c_84024, plain, (![A_2543]: (v1_tops_1(u1_struct_0(A_2543), A_2543) | ~v1_tops_1('#skF_1'(A_2543), A_2543) | ~m1_subset_1('#skF_1'(A_2543), k1_zfmisc_1(u1_struct_0(A_2543))) | ~l1_pre_topc(A_2543))), inference(resolution, [status(thm)], [c_56, c_77506])).
% 25.39/16.27  tff(c_84062, plain, (![A_2544]: (v1_tops_1(u1_struct_0(A_2544), A_2544) | ~v1_tops_1('#skF_1'(A_2544), A_2544) | ~l1_pre_topc(A_2544))), inference(resolution, [status(thm)], [c_24, c_84024])).
% 25.39/16.27  tff(c_67804, plain, (![A_1924, B_1925]: (k2_pre_topc(A_1924, B_1925)=k2_struct_0(A_1924) | ~v1_tops_1(B_1925, A_1924) | ~m1_subset_1(B_1925, k1_zfmisc_1(u1_struct_0(A_1924))) | ~l1_pre_topc(A_1924))), inference(cnfTransformation, [status(thm)], [f_72])).
% 25.39/16.27  tff(c_67838, plain, (![A_1924]: (k2_pre_topc(A_1924, u1_struct_0(A_1924))=k2_struct_0(A_1924) | ~v1_tops_1(u1_struct_0(A_1924), A_1924) | ~l1_pre_topc(A_1924))), inference(resolution, [status(thm)], [c_56, c_67804])).
% 25.39/16.27  tff(c_84099, plain, (![A_2545]: (k2_pre_topc(A_2545, u1_struct_0(A_2545))=k2_struct_0(A_2545) | ~v1_tops_1('#skF_1'(A_2545), A_2545) | ~l1_pre_topc(A_2545))), inference(resolution, [status(thm)], [c_84062, c_67838])).
% 25.39/16.27  tff(c_84138, plain, (![A_2547]: (k2_pre_topc(A_2547, u1_struct_0(A_2547))=k2_struct_0(A_2547) | ~l1_pre_topc(A_2547))), inference(resolution, [status(thm)], [c_22, c_84099])).
% 25.39/16.27  tff(c_67548, plain, (![A_5]: (r1_tarski(A_5, A_5))), inference(resolution, [status(thm)], [c_56, c_67532])).
% 25.39/16.27  tff(c_67656, plain, (![B_1911, A_1912]: (r1_tarski(B_1911, k2_pre_topc(A_1912, B_1911)) | ~m1_subset_1(B_1911, k1_zfmisc_1(u1_struct_0(A_1912))) | ~l1_pre_topc(A_1912))), inference(cnfTransformation, [status(thm)], [f_63])).
% 25.39/16.27  tff(c_67759, plain, (![A_1920]: (r1_tarski(u1_struct_0(A_1920), k2_pre_topc(A_1920, u1_struct_0(A_1920))) | ~l1_pre_topc(A_1920))), inference(resolution, [status(thm)], [c_56, c_67656])).
% 25.39/16.27  tff(c_68269, plain, (![A_1954, A_1955]: (r1_tarski(A_1954, k2_pre_topc(A_1955, u1_struct_0(A_1955))) | ~r1_tarski(A_1954, u1_struct_0(A_1955)) | ~l1_pre_topc(A_1955))), inference(resolution, [status(thm)], [c_67759, c_2])).
% 25.39/16.27  tff(c_75371, plain, (![A_2248, A_2249, A_2250]: (r1_tarski(A_2248, k2_pre_topc(A_2249, u1_struct_0(A_2249))) | ~r1_tarski(A_2248, A_2250) | ~r1_tarski(A_2250, u1_struct_0(A_2249)) | ~l1_pre_topc(A_2249))), inference(resolution, [status(thm)], [c_68269, c_2])).
% 25.39/16.27  tff(c_75585, plain, (![A_2251]: (r1_tarski('#skF_6', k2_pre_topc(A_2251, u1_struct_0(A_2251))) | ~r1_tarski(u1_struct_0('#skF_4'), u1_struct_0(A_2251)) | ~l1_pre_topc(A_2251))), inference(resolution, [status(thm)], [c_67546, c_75371])).
% 25.39/16.27  tff(c_75623, plain, (r1_tarski('#skF_6', k2_pre_topc('#skF_4', u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_67548, c_75585])).
% 25.39/16.27  tff(c_75648, plain, (r1_tarski('#skF_6', k2_pre_topc('#skF_4', u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_67556, c_75623])).
% 25.39/16.27  tff(c_84312, plain, (r1_tarski('#skF_6', k2_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_84138, c_75648])).
% 25.39/16.27  tff(c_84493, plain, (r1_tarski('#skF_6', k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_67556, c_84312])).
% 25.39/16.27  tff(c_84495, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68971, c_84493])).
% 25.39/16.27  tff(c_84616, plain, (![A_2551]: (~v2_compts_1('#skF_6', A_2551) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0(A_2551))) | ~m1_pre_topc('#skF_4', A_2551) | ~l1_pre_topc(A_2551))), inference(splitRight, [status(thm)], [c_68925])).
% 25.39/16.27  tff(c_84620, plain, (~v2_compts_1('#skF_6', '#skF_3') | ~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~r1_tarski('#skF_6', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_68935, c_84616])).
% 25.39/16.27  tff(c_84639, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_67546, c_44, c_42, c_67527, c_84620])).
% 25.39/16.27  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 25.39/16.27  
% 25.39/16.27  Inference rules
% 25.39/16.27  ----------------------
% 25.39/16.27  #Ref     : 0
% 25.39/16.27  #Sup     : 20824
% 25.39/16.27  #Fact    : 0
% 25.39/16.27  #Define  : 0
% 25.39/16.27  #Split   : 102
% 25.39/16.27  #Chain   : 0
% 25.39/16.27  #Close   : 0
% 25.39/16.27  
% 25.39/16.27  Ordering : KBO
% 25.39/16.27  
% 25.39/16.27  Simplification rules
% 25.39/16.27  ----------------------
% 25.39/16.27  #Subsume      : 10148
% 25.39/16.27  #Demod        : 6248
% 25.39/16.27  #Tautology    : 1291
% 25.39/16.27  #SimpNegUnit  : 282
% 25.39/16.27  #BackRed      : 0
% 25.39/16.27  
% 25.39/16.27  #Partial instantiations: 0
% 25.39/16.27  #Strategies tried      : 1
% 25.39/16.27  
% 25.39/16.27  Timing (in seconds)
% 25.39/16.27  ----------------------
% 25.39/16.27  Preprocessing        : 0.32
% 25.39/16.27  Parsing              : 0.17
% 25.39/16.27  CNF conversion       : 0.02
% 25.39/16.27  Main loop            : 15.09
% 25.39/16.27  Inferencing          : 2.63
% 25.39/16.27  Reduction            : 4.05
% 25.39/16.27  Demodulation         : 2.59
% 25.39/16.27  BG Simplification    : 0.18
% 25.39/16.27  Subsumption          : 7.37
% 25.39/16.27  Abstraction          : 0.35
% 25.39/16.27  MUC search           : 0.00
% 25.39/16.27  Cooper               : 0.00
% 25.39/16.27  Total                : 15.47
% 25.39/16.27  Index Insertion      : 0.00
% 25.39/16.27  Index Deletion       : 0.00
% 25.39/16.27  Index Matching       : 0.00
% 25.39/16.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
