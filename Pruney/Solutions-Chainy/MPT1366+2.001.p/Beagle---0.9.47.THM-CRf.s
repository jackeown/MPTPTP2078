%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:59 EST 2020

% Result     : Theorem 2.63s
% Output     : CNFRefutation 2.63s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 111 expanded)
%              Number of leaves         :   31 (  57 expanded)
%              Depth                    :   16
%              Number of atoms          :  356 ( 710 expanded)
%              Number of equality atoms :   31 (  48 expanded)
%              Maximal formula depth    :   22 (   7 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_pre_topc > v2_compts_1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v9_pre_topc > v8_pre_topc > v2_struct_0 > v2_pre_topc > v1_compts_1 > l1_pre_topc > k3_subset_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_6 > #skF_7 > #skF_5 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v8_pre_topc,type,(
    v8_pre_topc: $i > $o )).

tff(v2_compts_1,type,(
    v2_compts_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#skF_4',type,(
    '#skF_4': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v9_pre_topc,type,(
    v9_pre_topc: $i > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_compts_1,type,(
    v1_compts_1: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_126,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ( ( v8_pre_topc(A)
            & v1_compts_1(A) )
         => v9_pre_topc(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_compts_1)).

tff(f_65,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( v9_pre_topc(A)
      <=> ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ~ ( C != k1_xboole_0
                    & v4_pre_topc(C,A)
                    & r2_hidden(B,k3_subset_1(u1_struct_0(A),C))
                    & ! [D] :
                        ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                       => ! [E] :
                            ( m1_subset_1(E,k1_zfmisc_1(u1_struct_0(A)))
                           => ~ ( v3_pre_topc(D,A)
                                & v3_pre_topc(E,A)
                                & r2_hidden(B,D)
                                & r1_tarski(C,E)
                                & r1_xboole_0(D,E) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_compts_1)).

tff(f_112,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v1_compts_1(A)
              & v4_pre_topc(B,A) )
           => v2_compts_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_compts_1)).

tff(f_101,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( v8_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v2_compts_1(B,A)
             => ( B = k1_xboole_0
                | ! [C] :
                    ( m1_subset_1(C,u1_struct_0(A))
                   => ~ ( r2_hidden(C,k3_subset_1(u1_struct_0(A),B))
                        & ! [D] :
                            ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                           => ! [E] :
                                ( m1_subset_1(E,k1_zfmisc_1(u1_struct_0(A)))
                               => ~ ( v3_pre_topc(D,A)
                                    & v3_pre_topc(E,A)
                                    & r2_hidden(C,D)
                                    & r1_tarski(B,E)
                                    & r1_xboole_0(D,E) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_compts_1)).

tff(c_54,plain,(
    ~ v2_struct_0('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_52,plain,(
    v2_pre_topc('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_50,plain,(
    l1_pre_topc('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_55,plain,(
    ! [A_90] :
      ( '#skF_4'(A_90) != k1_xboole_0
      | v9_pre_topc(A_90)
      | ~ l1_pre_topc(A_90)
      | ~ v2_pre_topc(A_90)
      | v2_struct_0(A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_44,plain,(
    ~ v9_pre_topc('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_58,plain,
    ( '#skF_4'('#skF_7') != k1_xboole_0
    | ~ l1_pre_topc('#skF_7')
    | ~ v2_pre_topc('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_55,c_44])).

tff(c_61,plain,
    ( '#skF_4'('#skF_7') != k1_xboole_0
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_58])).

tff(c_62,plain,(
    '#skF_4'('#skF_7') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_61])).

tff(c_46,plain,(
    v1_compts_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_48,plain,(
    v8_pre_topc('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_6,plain,(
    ! [A_1] :
      ( v4_pre_topc('#skF_4'(A_1),A_1)
      | v9_pre_topc(A_1)
      | ~ l1_pre_topc(A_1)
      | ~ v2_pre_topc(A_1)
      | v2_struct_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_10,plain,(
    ! [A_1] :
      ( m1_subset_1('#skF_4'(A_1),k1_zfmisc_1(u1_struct_0(A_1)))
      | v9_pre_topc(A_1)
      | ~ l1_pre_topc(A_1)
      | ~ v2_pre_topc(A_1)
      | v2_struct_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_66,plain,(
    ! [B_94,A_95] :
      ( v2_compts_1(B_94,A_95)
      | ~ v4_pre_topc(B_94,A_95)
      | ~ v1_compts_1(A_95)
      | ~ m1_subset_1(B_94,k1_zfmisc_1(u1_struct_0(A_95)))
      | ~ l1_pre_topc(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_72,plain,(
    ! [A_97] :
      ( v2_compts_1('#skF_4'(A_97),A_97)
      | ~ v4_pre_topc('#skF_4'(A_97),A_97)
      | ~ v1_compts_1(A_97)
      | v9_pre_topc(A_97)
      | ~ l1_pre_topc(A_97)
      | ~ v2_pre_topc(A_97)
      | v2_struct_0(A_97) ) ),
    inference(resolution,[status(thm)],[c_10,c_66])).

tff(c_76,plain,(
    ! [A_1] :
      ( v2_compts_1('#skF_4'(A_1),A_1)
      | ~ v1_compts_1(A_1)
      | v9_pre_topc(A_1)
      | ~ l1_pre_topc(A_1)
      | ~ v2_pre_topc(A_1)
      | v2_struct_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_6,c_72])).

tff(c_12,plain,(
    ! [A_1] :
      ( m1_subset_1('#skF_3'(A_1),u1_struct_0(A_1))
      | v9_pre_topc(A_1)
      | ~ l1_pre_topc(A_1)
      | ~ v2_pre_topc(A_1)
      | v2_struct_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_4,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_3'(A_1),k3_subset_1(u1_struct_0(A_1),'#skF_4'(A_1)))
      | v9_pre_topc(A_1)
      | ~ l1_pre_topc(A_1)
      | ~ v2_pre_topc(A_1)
      | v2_struct_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_82,plain,(
    ! [A_102,B_103,C_104] :
      ( v3_pre_topc('#skF_5'(A_102,B_103,C_104),A_102)
      | ~ r2_hidden(C_104,k3_subset_1(u1_struct_0(A_102),B_103))
      | ~ m1_subset_1(C_104,u1_struct_0(A_102))
      | k1_xboole_0 = B_103
      | ~ v2_compts_1(B_103,A_102)
      | ~ m1_subset_1(B_103,k1_zfmisc_1(u1_struct_0(A_102)))
      | ~ v8_pre_topc(A_102)
      | ~ l1_pre_topc(A_102)
      | ~ v2_pre_topc(A_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_85,plain,(
    ! [A_1] :
      ( v3_pre_topc('#skF_5'(A_1,'#skF_4'(A_1),'#skF_3'(A_1)),A_1)
      | ~ m1_subset_1('#skF_3'(A_1),u1_struct_0(A_1))
      | '#skF_4'(A_1) = k1_xboole_0
      | ~ v2_compts_1('#skF_4'(A_1),A_1)
      | ~ m1_subset_1('#skF_4'(A_1),k1_zfmisc_1(u1_struct_0(A_1)))
      | ~ v8_pre_topc(A_1)
      | v9_pre_topc(A_1)
      | ~ l1_pre_topc(A_1)
      | ~ v2_pre_topc(A_1)
      | v2_struct_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_82])).

tff(c_90,plain,(
    ! [A_108,B_109,C_110] :
      ( v3_pre_topc('#skF_6'(A_108,B_109,C_110),A_108)
      | ~ r2_hidden(C_110,k3_subset_1(u1_struct_0(A_108),B_109))
      | ~ m1_subset_1(C_110,u1_struct_0(A_108))
      | k1_xboole_0 = B_109
      | ~ v2_compts_1(B_109,A_108)
      | ~ m1_subset_1(B_109,k1_zfmisc_1(u1_struct_0(A_108)))
      | ~ v8_pre_topc(A_108)
      | ~ l1_pre_topc(A_108)
      | ~ v2_pre_topc(A_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_93,plain,(
    ! [A_1] :
      ( v3_pre_topc('#skF_6'(A_1,'#skF_4'(A_1),'#skF_3'(A_1)),A_1)
      | ~ m1_subset_1('#skF_3'(A_1),u1_struct_0(A_1))
      | '#skF_4'(A_1) = k1_xboole_0
      | ~ v2_compts_1('#skF_4'(A_1),A_1)
      | ~ m1_subset_1('#skF_4'(A_1),k1_zfmisc_1(u1_struct_0(A_1)))
      | ~ v8_pre_topc(A_1)
      | v9_pre_topc(A_1)
      | ~ l1_pre_topc(A_1)
      | ~ v2_pre_topc(A_1)
      | v2_struct_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_90])).

tff(c_86,plain,(
    ! [B_105,A_106,C_107] :
      ( r1_tarski(B_105,'#skF_6'(A_106,B_105,C_107))
      | ~ r2_hidden(C_107,k3_subset_1(u1_struct_0(A_106),B_105))
      | ~ m1_subset_1(C_107,u1_struct_0(A_106))
      | k1_xboole_0 = B_105
      | ~ v2_compts_1(B_105,A_106)
      | ~ m1_subset_1(B_105,k1_zfmisc_1(u1_struct_0(A_106)))
      | ~ v8_pre_topc(A_106)
      | ~ l1_pre_topc(A_106)
      | ~ v2_pre_topc(A_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_89,plain,(
    ! [A_1] :
      ( r1_tarski('#skF_4'(A_1),'#skF_6'(A_1,'#skF_4'(A_1),'#skF_3'(A_1)))
      | ~ m1_subset_1('#skF_3'(A_1),u1_struct_0(A_1))
      | '#skF_4'(A_1) = k1_xboole_0
      | ~ v2_compts_1('#skF_4'(A_1),A_1)
      | ~ m1_subset_1('#skF_4'(A_1),k1_zfmisc_1(u1_struct_0(A_1)))
      | ~ v8_pre_topc(A_1)
      | v9_pre_topc(A_1)
      | ~ l1_pre_topc(A_1)
      | ~ v2_pre_topc(A_1)
      | v2_struct_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_86])).

tff(c_78,plain,(
    ! [C_99,A_100,B_101] :
      ( r2_hidden(C_99,'#skF_5'(A_100,B_101,C_99))
      | ~ r2_hidden(C_99,k3_subset_1(u1_struct_0(A_100),B_101))
      | ~ m1_subset_1(C_99,u1_struct_0(A_100))
      | k1_xboole_0 = B_101
      | ~ v2_compts_1(B_101,A_100)
      | ~ m1_subset_1(B_101,k1_zfmisc_1(u1_struct_0(A_100)))
      | ~ v8_pre_topc(A_100)
      | ~ l1_pre_topc(A_100)
      | ~ v2_pre_topc(A_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_81,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_3'(A_1),'#skF_5'(A_1,'#skF_4'(A_1),'#skF_3'(A_1)))
      | ~ m1_subset_1('#skF_3'(A_1),u1_struct_0(A_1))
      | '#skF_4'(A_1) = k1_xboole_0
      | ~ v2_compts_1('#skF_4'(A_1),A_1)
      | ~ m1_subset_1('#skF_4'(A_1),k1_zfmisc_1(u1_struct_0(A_1)))
      | ~ v8_pre_topc(A_1)
      | v9_pre_topc(A_1)
      | ~ l1_pre_topc(A_1)
      | ~ v2_pre_topc(A_1)
      | v2_struct_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_78])).

tff(c_40,plain,(
    ! [A_58,B_74,C_82] :
      ( m1_subset_1('#skF_5'(A_58,B_74,C_82),k1_zfmisc_1(u1_struct_0(A_58)))
      | ~ r2_hidden(C_82,k3_subset_1(u1_struct_0(A_58),B_74))
      | ~ m1_subset_1(C_82,u1_struct_0(A_58))
      | k1_xboole_0 = B_74
      | ~ v2_compts_1(B_74,A_58)
      | ~ m1_subset_1(B_74,k1_zfmisc_1(u1_struct_0(A_58)))
      | ~ v8_pre_topc(A_58)
      | ~ l1_pre_topc(A_58)
      | ~ v2_pre_topc(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_38,plain,(
    ! [A_58,B_74,C_82] :
      ( m1_subset_1('#skF_6'(A_58,B_74,C_82),k1_zfmisc_1(u1_struct_0(A_58)))
      | ~ r2_hidden(C_82,k3_subset_1(u1_struct_0(A_58),B_74))
      | ~ m1_subset_1(C_82,u1_struct_0(A_58))
      | k1_xboole_0 = B_74
      | ~ v2_compts_1(B_74,A_58)
      | ~ m1_subset_1(B_74,k1_zfmisc_1(u1_struct_0(A_58)))
      | ~ v8_pre_topc(A_58)
      | ~ l1_pre_topc(A_58)
      | ~ v2_pre_topc(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_120,plain,(
    ! [A_129,B_130,C_131] :
      ( r1_xboole_0('#skF_5'(A_129,B_130,C_131),'#skF_6'(A_129,B_130,C_131))
      | ~ r2_hidden(C_131,k3_subset_1(u1_struct_0(A_129),B_130))
      | ~ m1_subset_1(C_131,u1_struct_0(A_129))
      | k1_xboole_0 = B_130
      | ~ v2_compts_1(B_130,A_129)
      | ~ m1_subset_1(B_130,k1_zfmisc_1(u1_struct_0(A_129)))
      | ~ v8_pre_topc(A_129)
      | ~ l1_pre_topc(A_129)
      | ~ v2_pre_topc(A_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_145,plain,(
    ! [A_154] :
      ( r1_xboole_0('#skF_5'(A_154,'#skF_4'(A_154),'#skF_3'(A_154)),'#skF_6'(A_154,'#skF_4'(A_154),'#skF_3'(A_154)))
      | ~ m1_subset_1('#skF_3'(A_154),u1_struct_0(A_154))
      | '#skF_4'(A_154) = k1_xboole_0
      | ~ v2_compts_1('#skF_4'(A_154),A_154)
      | ~ m1_subset_1('#skF_4'(A_154),k1_zfmisc_1(u1_struct_0(A_154)))
      | ~ v8_pre_topc(A_154)
      | v9_pre_topc(A_154)
      | ~ l1_pre_topc(A_154)
      | ~ v2_pre_topc(A_154)
      | v2_struct_0(A_154) ) ),
    inference(resolution,[status(thm)],[c_4,c_120])).

tff(c_2,plain,(
    ! [D_55,E_57,A_1] :
      ( ~ r1_xboole_0(D_55,E_57)
      | ~ r1_tarski('#skF_4'(A_1),E_57)
      | ~ r2_hidden('#skF_3'(A_1),D_55)
      | ~ v3_pre_topc(E_57,A_1)
      | ~ v3_pre_topc(D_55,A_1)
      | ~ m1_subset_1(E_57,k1_zfmisc_1(u1_struct_0(A_1)))
      | ~ m1_subset_1(D_55,k1_zfmisc_1(u1_struct_0(A_1)))
      | v9_pre_topc(A_1)
      | ~ l1_pre_topc(A_1)
      | ~ v2_pre_topc(A_1)
      | v2_struct_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_151,plain,(
    ! [A_161,A_162] :
      ( ~ r1_tarski('#skF_4'(A_161),'#skF_6'(A_162,'#skF_4'(A_162),'#skF_3'(A_162)))
      | ~ r2_hidden('#skF_3'(A_161),'#skF_5'(A_162,'#skF_4'(A_162),'#skF_3'(A_162)))
      | ~ v3_pre_topc('#skF_6'(A_162,'#skF_4'(A_162),'#skF_3'(A_162)),A_161)
      | ~ v3_pre_topc('#skF_5'(A_162,'#skF_4'(A_162),'#skF_3'(A_162)),A_161)
      | ~ m1_subset_1('#skF_6'(A_162,'#skF_4'(A_162),'#skF_3'(A_162)),k1_zfmisc_1(u1_struct_0(A_161)))
      | ~ m1_subset_1('#skF_5'(A_162,'#skF_4'(A_162),'#skF_3'(A_162)),k1_zfmisc_1(u1_struct_0(A_161)))
      | v9_pre_topc(A_161)
      | ~ l1_pre_topc(A_161)
      | ~ v2_pre_topc(A_161)
      | v2_struct_0(A_161)
      | ~ m1_subset_1('#skF_3'(A_162),u1_struct_0(A_162))
      | '#skF_4'(A_162) = k1_xboole_0
      | ~ v2_compts_1('#skF_4'(A_162),A_162)
      | ~ m1_subset_1('#skF_4'(A_162),k1_zfmisc_1(u1_struct_0(A_162)))
      | ~ v8_pre_topc(A_162)
      | v9_pre_topc(A_162)
      | ~ l1_pre_topc(A_162)
      | ~ v2_pre_topc(A_162)
      | v2_struct_0(A_162) ) ),
    inference(resolution,[status(thm)],[c_145,c_2])).

tff(c_157,plain,(
    ! [A_163] :
      ( ~ r1_tarski('#skF_4'(A_163),'#skF_6'(A_163,'#skF_4'(A_163),'#skF_3'(A_163)))
      | ~ r2_hidden('#skF_3'(A_163),'#skF_5'(A_163,'#skF_4'(A_163),'#skF_3'(A_163)))
      | ~ v3_pre_topc('#skF_6'(A_163,'#skF_4'(A_163),'#skF_3'(A_163)),A_163)
      | ~ v3_pre_topc('#skF_5'(A_163,'#skF_4'(A_163),'#skF_3'(A_163)),A_163)
      | ~ m1_subset_1('#skF_5'(A_163,'#skF_4'(A_163),'#skF_3'(A_163)),k1_zfmisc_1(u1_struct_0(A_163)))
      | v9_pre_topc(A_163)
      | v2_struct_0(A_163)
      | ~ r2_hidden('#skF_3'(A_163),k3_subset_1(u1_struct_0(A_163),'#skF_4'(A_163)))
      | ~ m1_subset_1('#skF_3'(A_163),u1_struct_0(A_163))
      | '#skF_4'(A_163) = k1_xboole_0
      | ~ v2_compts_1('#skF_4'(A_163),A_163)
      | ~ m1_subset_1('#skF_4'(A_163),k1_zfmisc_1(u1_struct_0(A_163)))
      | ~ v8_pre_topc(A_163)
      | ~ l1_pre_topc(A_163)
      | ~ v2_pre_topc(A_163) ) ),
    inference(resolution,[status(thm)],[c_38,c_151])).

tff(c_163,plain,(
    ! [A_164] :
      ( ~ r1_tarski('#skF_4'(A_164),'#skF_6'(A_164,'#skF_4'(A_164),'#skF_3'(A_164)))
      | ~ r2_hidden('#skF_3'(A_164),'#skF_5'(A_164,'#skF_4'(A_164),'#skF_3'(A_164)))
      | ~ v3_pre_topc('#skF_6'(A_164,'#skF_4'(A_164),'#skF_3'(A_164)),A_164)
      | ~ v3_pre_topc('#skF_5'(A_164,'#skF_4'(A_164),'#skF_3'(A_164)),A_164)
      | v9_pre_topc(A_164)
      | v2_struct_0(A_164)
      | ~ r2_hidden('#skF_3'(A_164),k3_subset_1(u1_struct_0(A_164),'#skF_4'(A_164)))
      | ~ m1_subset_1('#skF_3'(A_164),u1_struct_0(A_164))
      | '#skF_4'(A_164) = k1_xboole_0
      | ~ v2_compts_1('#skF_4'(A_164),A_164)
      | ~ m1_subset_1('#skF_4'(A_164),k1_zfmisc_1(u1_struct_0(A_164)))
      | ~ v8_pre_topc(A_164)
      | ~ l1_pre_topc(A_164)
      | ~ v2_pre_topc(A_164) ) ),
    inference(resolution,[status(thm)],[c_40,c_157])).

tff(c_167,plain,(
    ! [A_165] :
      ( ~ r1_tarski('#skF_4'(A_165),'#skF_6'(A_165,'#skF_4'(A_165),'#skF_3'(A_165)))
      | ~ v3_pre_topc('#skF_6'(A_165,'#skF_4'(A_165),'#skF_3'(A_165)),A_165)
      | ~ v3_pre_topc('#skF_5'(A_165,'#skF_4'(A_165),'#skF_3'(A_165)),A_165)
      | ~ r2_hidden('#skF_3'(A_165),k3_subset_1(u1_struct_0(A_165),'#skF_4'(A_165)))
      | ~ m1_subset_1('#skF_3'(A_165),u1_struct_0(A_165))
      | '#skF_4'(A_165) = k1_xboole_0
      | ~ v2_compts_1('#skF_4'(A_165),A_165)
      | ~ m1_subset_1('#skF_4'(A_165),k1_zfmisc_1(u1_struct_0(A_165)))
      | ~ v8_pre_topc(A_165)
      | v9_pre_topc(A_165)
      | ~ l1_pre_topc(A_165)
      | ~ v2_pre_topc(A_165)
      | v2_struct_0(A_165) ) ),
    inference(resolution,[status(thm)],[c_81,c_163])).

tff(c_171,plain,(
    ! [A_166] :
      ( ~ v3_pre_topc('#skF_6'(A_166,'#skF_4'(A_166),'#skF_3'(A_166)),A_166)
      | ~ v3_pre_topc('#skF_5'(A_166,'#skF_4'(A_166),'#skF_3'(A_166)),A_166)
      | ~ r2_hidden('#skF_3'(A_166),k3_subset_1(u1_struct_0(A_166),'#skF_4'(A_166)))
      | ~ m1_subset_1('#skF_3'(A_166),u1_struct_0(A_166))
      | '#skF_4'(A_166) = k1_xboole_0
      | ~ v2_compts_1('#skF_4'(A_166),A_166)
      | ~ m1_subset_1('#skF_4'(A_166),k1_zfmisc_1(u1_struct_0(A_166)))
      | ~ v8_pre_topc(A_166)
      | v9_pre_topc(A_166)
      | ~ l1_pre_topc(A_166)
      | ~ v2_pre_topc(A_166)
      | v2_struct_0(A_166) ) ),
    inference(resolution,[status(thm)],[c_89,c_167])).

tff(c_175,plain,(
    ! [A_167] :
      ( ~ v3_pre_topc('#skF_5'(A_167,'#skF_4'(A_167),'#skF_3'(A_167)),A_167)
      | ~ r2_hidden('#skF_3'(A_167),k3_subset_1(u1_struct_0(A_167),'#skF_4'(A_167)))
      | ~ m1_subset_1('#skF_3'(A_167),u1_struct_0(A_167))
      | '#skF_4'(A_167) = k1_xboole_0
      | ~ v2_compts_1('#skF_4'(A_167),A_167)
      | ~ m1_subset_1('#skF_4'(A_167),k1_zfmisc_1(u1_struct_0(A_167)))
      | ~ v8_pre_topc(A_167)
      | v9_pre_topc(A_167)
      | ~ l1_pre_topc(A_167)
      | ~ v2_pre_topc(A_167)
      | v2_struct_0(A_167) ) ),
    inference(resolution,[status(thm)],[c_93,c_171])).

tff(c_179,plain,(
    ! [A_168] :
      ( ~ r2_hidden('#skF_3'(A_168),k3_subset_1(u1_struct_0(A_168),'#skF_4'(A_168)))
      | ~ m1_subset_1('#skF_3'(A_168),u1_struct_0(A_168))
      | '#skF_4'(A_168) = k1_xboole_0
      | ~ v2_compts_1('#skF_4'(A_168),A_168)
      | ~ m1_subset_1('#skF_4'(A_168),k1_zfmisc_1(u1_struct_0(A_168)))
      | ~ v8_pre_topc(A_168)
      | v9_pre_topc(A_168)
      | ~ l1_pre_topc(A_168)
      | ~ v2_pre_topc(A_168)
      | v2_struct_0(A_168) ) ),
    inference(resolution,[status(thm)],[c_85,c_175])).

tff(c_184,plain,(
    ! [A_169] :
      ( ~ m1_subset_1('#skF_3'(A_169),u1_struct_0(A_169))
      | '#skF_4'(A_169) = k1_xboole_0
      | ~ v2_compts_1('#skF_4'(A_169),A_169)
      | ~ m1_subset_1('#skF_4'(A_169),k1_zfmisc_1(u1_struct_0(A_169)))
      | ~ v8_pre_topc(A_169)
      | v9_pre_topc(A_169)
      | ~ l1_pre_topc(A_169)
      | ~ v2_pre_topc(A_169)
      | v2_struct_0(A_169) ) ),
    inference(resolution,[status(thm)],[c_4,c_179])).

tff(c_189,plain,(
    ! [A_170] :
      ( ~ m1_subset_1('#skF_3'(A_170),u1_struct_0(A_170))
      | '#skF_4'(A_170) = k1_xboole_0
      | ~ v2_compts_1('#skF_4'(A_170),A_170)
      | ~ v8_pre_topc(A_170)
      | v9_pre_topc(A_170)
      | ~ l1_pre_topc(A_170)
      | ~ v2_pre_topc(A_170)
      | v2_struct_0(A_170) ) ),
    inference(resolution,[status(thm)],[c_10,c_184])).

tff(c_194,plain,(
    ! [A_171] :
      ( '#skF_4'(A_171) = k1_xboole_0
      | ~ v2_compts_1('#skF_4'(A_171),A_171)
      | ~ v8_pre_topc(A_171)
      | v9_pre_topc(A_171)
      | ~ l1_pre_topc(A_171)
      | ~ v2_pre_topc(A_171)
      | v2_struct_0(A_171) ) ),
    inference(resolution,[status(thm)],[c_12,c_189])).

tff(c_199,plain,(
    ! [A_172] :
      ( '#skF_4'(A_172) = k1_xboole_0
      | ~ v8_pre_topc(A_172)
      | ~ v1_compts_1(A_172)
      | v9_pre_topc(A_172)
      | ~ l1_pre_topc(A_172)
      | ~ v2_pre_topc(A_172)
      | v2_struct_0(A_172) ) ),
    inference(resolution,[status(thm)],[c_76,c_194])).

tff(c_202,plain,
    ( '#skF_4'('#skF_7') = k1_xboole_0
    | ~ v8_pre_topc('#skF_7')
    | ~ v1_compts_1('#skF_7')
    | ~ l1_pre_topc('#skF_7')
    | ~ v2_pre_topc('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_199,c_44])).

tff(c_205,plain,
    ( '#skF_4'('#skF_7') = k1_xboole_0
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_46,c_48,c_202])).

tff(c_207,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_62,c_205])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 13:31:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.63/1.40  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.63/1.41  
% 2.63/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.63/1.41  %$ v4_pre_topc > v3_pre_topc > v2_compts_1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v9_pre_topc > v8_pre_topc > v2_struct_0 > v2_pre_topc > v1_compts_1 > l1_pre_topc > k3_subset_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_6 > #skF_7 > #skF_5 > #skF_2 > #skF_3
% 2.63/1.41  
% 2.63/1.41  %Foreground sorts:
% 2.63/1.41  
% 2.63/1.41  
% 2.63/1.41  %Background operators:
% 2.63/1.41  
% 2.63/1.41  
% 2.63/1.41  %Foreground operators:
% 2.63/1.41  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.63/1.41  tff(v8_pre_topc, type, v8_pre_topc: $i > $o).
% 2.63/1.41  tff(v2_compts_1, type, v2_compts_1: ($i * $i) > $o).
% 2.63/1.41  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.63/1.41  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.63/1.41  tff('#skF_4', type, '#skF_4': $i > $i).
% 2.63/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.63/1.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.63/1.41  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 2.63/1.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.63/1.41  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.63/1.41  tff('#skF_7', type, '#skF_7': $i).
% 2.63/1.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.63/1.41  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.63/1.41  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 2.63/1.41  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.63/1.41  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.63/1.41  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.63/1.41  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.63/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.63/1.41  tff('#skF_3', type, '#skF_3': $i > $i).
% 2.63/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.63/1.41  tff(v9_pre_topc, type, v9_pre_topc: $i > $o).
% 2.63/1.41  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.63/1.41  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.63/1.41  tff(v1_compts_1, type, v1_compts_1: $i > $o).
% 2.63/1.41  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.63/1.41  
% 2.63/1.43  tff(f_126, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => ((v8_pre_topc(A) & v1_compts_1(A)) => v9_pre_topc(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_compts_1)).
% 2.63/1.43  tff(f_65, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (v9_pre_topc(A) <=> (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(((~(C = k1_xboole_0) & v4_pre_topc(C, A)) & r2_hidden(B, k3_subset_1(u1_struct_0(A), C))) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(A))) => ~((((v3_pre_topc(D, A) & v3_pre_topc(E, A)) & r2_hidden(B, D)) & r1_tarski(C, E)) & r1_xboole_0(D, E)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_compts_1)).
% 2.63/1.43  tff(f_112, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v1_compts_1(A) & v4_pre_topc(B, A)) => v2_compts_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_compts_1)).
% 2.63/1.43  tff(f_101, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (v8_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_compts_1(B, A) => ((B = k1_xboole_0) | (![C]: (m1_subset_1(C, u1_struct_0(A)) => ~(r2_hidden(C, k3_subset_1(u1_struct_0(A), B)) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(A))) => ~((((v3_pre_topc(D, A) & v3_pre_topc(E, A)) & r2_hidden(C, D)) & r1_tarski(B, E)) & r1_xboole_0(D, E)))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_compts_1)).
% 2.63/1.43  tff(c_54, plain, (~v2_struct_0('#skF_7')), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.63/1.43  tff(c_52, plain, (v2_pre_topc('#skF_7')), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.63/1.43  tff(c_50, plain, (l1_pre_topc('#skF_7')), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.63/1.43  tff(c_55, plain, (![A_90]: ('#skF_4'(A_90)!=k1_xboole_0 | v9_pre_topc(A_90) | ~l1_pre_topc(A_90) | ~v2_pre_topc(A_90) | v2_struct_0(A_90))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.63/1.43  tff(c_44, plain, (~v9_pre_topc('#skF_7')), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.63/1.43  tff(c_58, plain, ('#skF_4'('#skF_7')!=k1_xboole_0 | ~l1_pre_topc('#skF_7') | ~v2_pre_topc('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_55, c_44])).
% 2.63/1.43  tff(c_61, plain, ('#skF_4'('#skF_7')!=k1_xboole_0 | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_58])).
% 2.63/1.43  tff(c_62, plain, ('#skF_4'('#skF_7')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_54, c_61])).
% 2.63/1.43  tff(c_46, plain, (v1_compts_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.63/1.43  tff(c_48, plain, (v8_pre_topc('#skF_7')), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.63/1.43  tff(c_6, plain, (![A_1]: (v4_pre_topc('#skF_4'(A_1), A_1) | v9_pre_topc(A_1) | ~l1_pre_topc(A_1) | ~v2_pre_topc(A_1) | v2_struct_0(A_1))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.63/1.43  tff(c_10, plain, (![A_1]: (m1_subset_1('#skF_4'(A_1), k1_zfmisc_1(u1_struct_0(A_1))) | v9_pre_topc(A_1) | ~l1_pre_topc(A_1) | ~v2_pre_topc(A_1) | v2_struct_0(A_1))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.63/1.43  tff(c_66, plain, (![B_94, A_95]: (v2_compts_1(B_94, A_95) | ~v4_pre_topc(B_94, A_95) | ~v1_compts_1(A_95) | ~m1_subset_1(B_94, k1_zfmisc_1(u1_struct_0(A_95))) | ~l1_pre_topc(A_95))), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.63/1.43  tff(c_72, plain, (![A_97]: (v2_compts_1('#skF_4'(A_97), A_97) | ~v4_pre_topc('#skF_4'(A_97), A_97) | ~v1_compts_1(A_97) | v9_pre_topc(A_97) | ~l1_pre_topc(A_97) | ~v2_pre_topc(A_97) | v2_struct_0(A_97))), inference(resolution, [status(thm)], [c_10, c_66])).
% 2.63/1.43  tff(c_76, plain, (![A_1]: (v2_compts_1('#skF_4'(A_1), A_1) | ~v1_compts_1(A_1) | v9_pre_topc(A_1) | ~l1_pre_topc(A_1) | ~v2_pre_topc(A_1) | v2_struct_0(A_1))), inference(resolution, [status(thm)], [c_6, c_72])).
% 2.63/1.43  tff(c_12, plain, (![A_1]: (m1_subset_1('#skF_3'(A_1), u1_struct_0(A_1)) | v9_pre_topc(A_1) | ~l1_pre_topc(A_1) | ~v2_pre_topc(A_1) | v2_struct_0(A_1))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.63/1.43  tff(c_4, plain, (![A_1]: (r2_hidden('#skF_3'(A_1), k3_subset_1(u1_struct_0(A_1), '#skF_4'(A_1))) | v9_pre_topc(A_1) | ~l1_pre_topc(A_1) | ~v2_pre_topc(A_1) | v2_struct_0(A_1))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.63/1.43  tff(c_82, plain, (![A_102, B_103, C_104]: (v3_pre_topc('#skF_5'(A_102, B_103, C_104), A_102) | ~r2_hidden(C_104, k3_subset_1(u1_struct_0(A_102), B_103)) | ~m1_subset_1(C_104, u1_struct_0(A_102)) | k1_xboole_0=B_103 | ~v2_compts_1(B_103, A_102) | ~m1_subset_1(B_103, k1_zfmisc_1(u1_struct_0(A_102))) | ~v8_pre_topc(A_102) | ~l1_pre_topc(A_102) | ~v2_pre_topc(A_102))), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.63/1.43  tff(c_85, plain, (![A_1]: (v3_pre_topc('#skF_5'(A_1, '#skF_4'(A_1), '#skF_3'(A_1)), A_1) | ~m1_subset_1('#skF_3'(A_1), u1_struct_0(A_1)) | '#skF_4'(A_1)=k1_xboole_0 | ~v2_compts_1('#skF_4'(A_1), A_1) | ~m1_subset_1('#skF_4'(A_1), k1_zfmisc_1(u1_struct_0(A_1))) | ~v8_pre_topc(A_1) | v9_pre_topc(A_1) | ~l1_pre_topc(A_1) | ~v2_pre_topc(A_1) | v2_struct_0(A_1))), inference(resolution, [status(thm)], [c_4, c_82])).
% 2.63/1.43  tff(c_90, plain, (![A_108, B_109, C_110]: (v3_pre_topc('#skF_6'(A_108, B_109, C_110), A_108) | ~r2_hidden(C_110, k3_subset_1(u1_struct_0(A_108), B_109)) | ~m1_subset_1(C_110, u1_struct_0(A_108)) | k1_xboole_0=B_109 | ~v2_compts_1(B_109, A_108) | ~m1_subset_1(B_109, k1_zfmisc_1(u1_struct_0(A_108))) | ~v8_pre_topc(A_108) | ~l1_pre_topc(A_108) | ~v2_pre_topc(A_108))), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.63/1.43  tff(c_93, plain, (![A_1]: (v3_pre_topc('#skF_6'(A_1, '#skF_4'(A_1), '#skF_3'(A_1)), A_1) | ~m1_subset_1('#skF_3'(A_1), u1_struct_0(A_1)) | '#skF_4'(A_1)=k1_xboole_0 | ~v2_compts_1('#skF_4'(A_1), A_1) | ~m1_subset_1('#skF_4'(A_1), k1_zfmisc_1(u1_struct_0(A_1))) | ~v8_pre_topc(A_1) | v9_pre_topc(A_1) | ~l1_pre_topc(A_1) | ~v2_pre_topc(A_1) | v2_struct_0(A_1))), inference(resolution, [status(thm)], [c_4, c_90])).
% 2.63/1.43  tff(c_86, plain, (![B_105, A_106, C_107]: (r1_tarski(B_105, '#skF_6'(A_106, B_105, C_107)) | ~r2_hidden(C_107, k3_subset_1(u1_struct_0(A_106), B_105)) | ~m1_subset_1(C_107, u1_struct_0(A_106)) | k1_xboole_0=B_105 | ~v2_compts_1(B_105, A_106) | ~m1_subset_1(B_105, k1_zfmisc_1(u1_struct_0(A_106))) | ~v8_pre_topc(A_106) | ~l1_pre_topc(A_106) | ~v2_pre_topc(A_106))), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.63/1.43  tff(c_89, plain, (![A_1]: (r1_tarski('#skF_4'(A_1), '#skF_6'(A_1, '#skF_4'(A_1), '#skF_3'(A_1))) | ~m1_subset_1('#skF_3'(A_1), u1_struct_0(A_1)) | '#skF_4'(A_1)=k1_xboole_0 | ~v2_compts_1('#skF_4'(A_1), A_1) | ~m1_subset_1('#skF_4'(A_1), k1_zfmisc_1(u1_struct_0(A_1))) | ~v8_pre_topc(A_1) | v9_pre_topc(A_1) | ~l1_pre_topc(A_1) | ~v2_pre_topc(A_1) | v2_struct_0(A_1))), inference(resolution, [status(thm)], [c_4, c_86])).
% 2.63/1.43  tff(c_78, plain, (![C_99, A_100, B_101]: (r2_hidden(C_99, '#skF_5'(A_100, B_101, C_99)) | ~r2_hidden(C_99, k3_subset_1(u1_struct_0(A_100), B_101)) | ~m1_subset_1(C_99, u1_struct_0(A_100)) | k1_xboole_0=B_101 | ~v2_compts_1(B_101, A_100) | ~m1_subset_1(B_101, k1_zfmisc_1(u1_struct_0(A_100))) | ~v8_pre_topc(A_100) | ~l1_pre_topc(A_100) | ~v2_pre_topc(A_100))), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.63/1.43  tff(c_81, plain, (![A_1]: (r2_hidden('#skF_3'(A_1), '#skF_5'(A_1, '#skF_4'(A_1), '#skF_3'(A_1))) | ~m1_subset_1('#skF_3'(A_1), u1_struct_0(A_1)) | '#skF_4'(A_1)=k1_xboole_0 | ~v2_compts_1('#skF_4'(A_1), A_1) | ~m1_subset_1('#skF_4'(A_1), k1_zfmisc_1(u1_struct_0(A_1))) | ~v8_pre_topc(A_1) | v9_pre_topc(A_1) | ~l1_pre_topc(A_1) | ~v2_pre_topc(A_1) | v2_struct_0(A_1))), inference(resolution, [status(thm)], [c_4, c_78])).
% 2.63/1.43  tff(c_40, plain, (![A_58, B_74, C_82]: (m1_subset_1('#skF_5'(A_58, B_74, C_82), k1_zfmisc_1(u1_struct_0(A_58))) | ~r2_hidden(C_82, k3_subset_1(u1_struct_0(A_58), B_74)) | ~m1_subset_1(C_82, u1_struct_0(A_58)) | k1_xboole_0=B_74 | ~v2_compts_1(B_74, A_58) | ~m1_subset_1(B_74, k1_zfmisc_1(u1_struct_0(A_58))) | ~v8_pre_topc(A_58) | ~l1_pre_topc(A_58) | ~v2_pre_topc(A_58))), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.63/1.43  tff(c_38, plain, (![A_58, B_74, C_82]: (m1_subset_1('#skF_6'(A_58, B_74, C_82), k1_zfmisc_1(u1_struct_0(A_58))) | ~r2_hidden(C_82, k3_subset_1(u1_struct_0(A_58), B_74)) | ~m1_subset_1(C_82, u1_struct_0(A_58)) | k1_xboole_0=B_74 | ~v2_compts_1(B_74, A_58) | ~m1_subset_1(B_74, k1_zfmisc_1(u1_struct_0(A_58))) | ~v8_pre_topc(A_58) | ~l1_pre_topc(A_58) | ~v2_pre_topc(A_58))), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.63/1.43  tff(c_120, plain, (![A_129, B_130, C_131]: (r1_xboole_0('#skF_5'(A_129, B_130, C_131), '#skF_6'(A_129, B_130, C_131)) | ~r2_hidden(C_131, k3_subset_1(u1_struct_0(A_129), B_130)) | ~m1_subset_1(C_131, u1_struct_0(A_129)) | k1_xboole_0=B_130 | ~v2_compts_1(B_130, A_129) | ~m1_subset_1(B_130, k1_zfmisc_1(u1_struct_0(A_129))) | ~v8_pre_topc(A_129) | ~l1_pre_topc(A_129) | ~v2_pre_topc(A_129))), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.63/1.43  tff(c_145, plain, (![A_154]: (r1_xboole_0('#skF_5'(A_154, '#skF_4'(A_154), '#skF_3'(A_154)), '#skF_6'(A_154, '#skF_4'(A_154), '#skF_3'(A_154))) | ~m1_subset_1('#skF_3'(A_154), u1_struct_0(A_154)) | '#skF_4'(A_154)=k1_xboole_0 | ~v2_compts_1('#skF_4'(A_154), A_154) | ~m1_subset_1('#skF_4'(A_154), k1_zfmisc_1(u1_struct_0(A_154))) | ~v8_pre_topc(A_154) | v9_pre_topc(A_154) | ~l1_pre_topc(A_154) | ~v2_pre_topc(A_154) | v2_struct_0(A_154))), inference(resolution, [status(thm)], [c_4, c_120])).
% 2.63/1.43  tff(c_2, plain, (![D_55, E_57, A_1]: (~r1_xboole_0(D_55, E_57) | ~r1_tarski('#skF_4'(A_1), E_57) | ~r2_hidden('#skF_3'(A_1), D_55) | ~v3_pre_topc(E_57, A_1) | ~v3_pre_topc(D_55, A_1) | ~m1_subset_1(E_57, k1_zfmisc_1(u1_struct_0(A_1))) | ~m1_subset_1(D_55, k1_zfmisc_1(u1_struct_0(A_1))) | v9_pre_topc(A_1) | ~l1_pre_topc(A_1) | ~v2_pre_topc(A_1) | v2_struct_0(A_1))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.63/1.43  tff(c_151, plain, (![A_161, A_162]: (~r1_tarski('#skF_4'(A_161), '#skF_6'(A_162, '#skF_4'(A_162), '#skF_3'(A_162))) | ~r2_hidden('#skF_3'(A_161), '#skF_5'(A_162, '#skF_4'(A_162), '#skF_3'(A_162))) | ~v3_pre_topc('#skF_6'(A_162, '#skF_4'(A_162), '#skF_3'(A_162)), A_161) | ~v3_pre_topc('#skF_5'(A_162, '#skF_4'(A_162), '#skF_3'(A_162)), A_161) | ~m1_subset_1('#skF_6'(A_162, '#skF_4'(A_162), '#skF_3'(A_162)), k1_zfmisc_1(u1_struct_0(A_161))) | ~m1_subset_1('#skF_5'(A_162, '#skF_4'(A_162), '#skF_3'(A_162)), k1_zfmisc_1(u1_struct_0(A_161))) | v9_pre_topc(A_161) | ~l1_pre_topc(A_161) | ~v2_pre_topc(A_161) | v2_struct_0(A_161) | ~m1_subset_1('#skF_3'(A_162), u1_struct_0(A_162)) | '#skF_4'(A_162)=k1_xboole_0 | ~v2_compts_1('#skF_4'(A_162), A_162) | ~m1_subset_1('#skF_4'(A_162), k1_zfmisc_1(u1_struct_0(A_162))) | ~v8_pre_topc(A_162) | v9_pre_topc(A_162) | ~l1_pre_topc(A_162) | ~v2_pre_topc(A_162) | v2_struct_0(A_162))), inference(resolution, [status(thm)], [c_145, c_2])).
% 2.63/1.43  tff(c_157, plain, (![A_163]: (~r1_tarski('#skF_4'(A_163), '#skF_6'(A_163, '#skF_4'(A_163), '#skF_3'(A_163))) | ~r2_hidden('#skF_3'(A_163), '#skF_5'(A_163, '#skF_4'(A_163), '#skF_3'(A_163))) | ~v3_pre_topc('#skF_6'(A_163, '#skF_4'(A_163), '#skF_3'(A_163)), A_163) | ~v3_pre_topc('#skF_5'(A_163, '#skF_4'(A_163), '#skF_3'(A_163)), A_163) | ~m1_subset_1('#skF_5'(A_163, '#skF_4'(A_163), '#skF_3'(A_163)), k1_zfmisc_1(u1_struct_0(A_163))) | v9_pre_topc(A_163) | v2_struct_0(A_163) | ~r2_hidden('#skF_3'(A_163), k3_subset_1(u1_struct_0(A_163), '#skF_4'(A_163))) | ~m1_subset_1('#skF_3'(A_163), u1_struct_0(A_163)) | '#skF_4'(A_163)=k1_xboole_0 | ~v2_compts_1('#skF_4'(A_163), A_163) | ~m1_subset_1('#skF_4'(A_163), k1_zfmisc_1(u1_struct_0(A_163))) | ~v8_pre_topc(A_163) | ~l1_pre_topc(A_163) | ~v2_pre_topc(A_163))), inference(resolution, [status(thm)], [c_38, c_151])).
% 2.63/1.43  tff(c_163, plain, (![A_164]: (~r1_tarski('#skF_4'(A_164), '#skF_6'(A_164, '#skF_4'(A_164), '#skF_3'(A_164))) | ~r2_hidden('#skF_3'(A_164), '#skF_5'(A_164, '#skF_4'(A_164), '#skF_3'(A_164))) | ~v3_pre_topc('#skF_6'(A_164, '#skF_4'(A_164), '#skF_3'(A_164)), A_164) | ~v3_pre_topc('#skF_5'(A_164, '#skF_4'(A_164), '#skF_3'(A_164)), A_164) | v9_pre_topc(A_164) | v2_struct_0(A_164) | ~r2_hidden('#skF_3'(A_164), k3_subset_1(u1_struct_0(A_164), '#skF_4'(A_164))) | ~m1_subset_1('#skF_3'(A_164), u1_struct_0(A_164)) | '#skF_4'(A_164)=k1_xboole_0 | ~v2_compts_1('#skF_4'(A_164), A_164) | ~m1_subset_1('#skF_4'(A_164), k1_zfmisc_1(u1_struct_0(A_164))) | ~v8_pre_topc(A_164) | ~l1_pre_topc(A_164) | ~v2_pre_topc(A_164))), inference(resolution, [status(thm)], [c_40, c_157])).
% 2.63/1.43  tff(c_167, plain, (![A_165]: (~r1_tarski('#skF_4'(A_165), '#skF_6'(A_165, '#skF_4'(A_165), '#skF_3'(A_165))) | ~v3_pre_topc('#skF_6'(A_165, '#skF_4'(A_165), '#skF_3'(A_165)), A_165) | ~v3_pre_topc('#skF_5'(A_165, '#skF_4'(A_165), '#skF_3'(A_165)), A_165) | ~r2_hidden('#skF_3'(A_165), k3_subset_1(u1_struct_0(A_165), '#skF_4'(A_165))) | ~m1_subset_1('#skF_3'(A_165), u1_struct_0(A_165)) | '#skF_4'(A_165)=k1_xboole_0 | ~v2_compts_1('#skF_4'(A_165), A_165) | ~m1_subset_1('#skF_4'(A_165), k1_zfmisc_1(u1_struct_0(A_165))) | ~v8_pre_topc(A_165) | v9_pre_topc(A_165) | ~l1_pre_topc(A_165) | ~v2_pre_topc(A_165) | v2_struct_0(A_165))), inference(resolution, [status(thm)], [c_81, c_163])).
% 2.63/1.43  tff(c_171, plain, (![A_166]: (~v3_pre_topc('#skF_6'(A_166, '#skF_4'(A_166), '#skF_3'(A_166)), A_166) | ~v3_pre_topc('#skF_5'(A_166, '#skF_4'(A_166), '#skF_3'(A_166)), A_166) | ~r2_hidden('#skF_3'(A_166), k3_subset_1(u1_struct_0(A_166), '#skF_4'(A_166))) | ~m1_subset_1('#skF_3'(A_166), u1_struct_0(A_166)) | '#skF_4'(A_166)=k1_xboole_0 | ~v2_compts_1('#skF_4'(A_166), A_166) | ~m1_subset_1('#skF_4'(A_166), k1_zfmisc_1(u1_struct_0(A_166))) | ~v8_pre_topc(A_166) | v9_pre_topc(A_166) | ~l1_pre_topc(A_166) | ~v2_pre_topc(A_166) | v2_struct_0(A_166))), inference(resolution, [status(thm)], [c_89, c_167])).
% 2.63/1.43  tff(c_175, plain, (![A_167]: (~v3_pre_topc('#skF_5'(A_167, '#skF_4'(A_167), '#skF_3'(A_167)), A_167) | ~r2_hidden('#skF_3'(A_167), k3_subset_1(u1_struct_0(A_167), '#skF_4'(A_167))) | ~m1_subset_1('#skF_3'(A_167), u1_struct_0(A_167)) | '#skF_4'(A_167)=k1_xboole_0 | ~v2_compts_1('#skF_4'(A_167), A_167) | ~m1_subset_1('#skF_4'(A_167), k1_zfmisc_1(u1_struct_0(A_167))) | ~v8_pre_topc(A_167) | v9_pre_topc(A_167) | ~l1_pre_topc(A_167) | ~v2_pre_topc(A_167) | v2_struct_0(A_167))), inference(resolution, [status(thm)], [c_93, c_171])).
% 2.63/1.43  tff(c_179, plain, (![A_168]: (~r2_hidden('#skF_3'(A_168), k3_subset_1(u1_struct_0(A_168), '#skF_4'(A_168))) | ~m1_subset_1('#skF_3'(A_168), u1_struct_0(A_168)) | '#skF_4'(A_168)=k1_xboole_0 | ~v2_compts_1('#skF_4'(A_168), A_168) | ~m1_subset_1('#skF_4'(A_168), k1_zfmisc_1(u1_struct_0(A_168))) | ~v8_pre_topc(A_168) | v9_pre_topc(A_168) | ~l1_pre_topc(A_168) | ~v2_pre_topc(A_168) | v2_struct_0(A_168))), inference(resolution, [status(thm)], [c_85, c_175])).
% 2.63/1.43  tff(c_184, plain, (![A_169]: (~m1_subset_1('#skF_3'(A_169), u1_struct_0(A_169)) | '#skF_4'(A_169)=k1_xboole_0 | ~v2_compts_1('#skF_4'(A_169), A_169) | ~m1_subset_1('#skF_4'(A_169), k1_zfmisc_1(u1_struct_0(A_169))) | ~v8_pre_topc(A_169) | v9_pre_topc(A_169) | ~l1_pre_topc(A_169) | ~v2_pre_topc(A_169) | v2_struct_0(A_169))), inference(resolution, [status(thm)], [c_4, c_179])).
% 2.63/1.43  tff(c_189, plain, (![A_170]: (~m1_subset_1('#skF_3'(A_170), u1_struct_0(A_170)) | '#skF_4'(A_170)=k1_xboole_0 | ~v2_compts_1('#skF_4'(A_170), A_170) | ~v8_pre_topc(A_170) | v9_pre_topc(A_170) | ~l1_pre_topc(A_170) | ~v2_pre_topc(A_170) | v2_struct_0(A_170))), inference(resolution, [status(thm)], [c_10, c_184])).
% 2.63/1.43  tff(c_194, plain, (![A_171]: ('#skF_4'(A_171)=k1_xboole_0 | ~v2_compts_1('#skF_4'(A_171), A_171) | ~v8_pre_topc(A_171) | v9_pre_topc(A_171) | ~l1_pre_topc(A_171) | ~v2_pre_topc(A_171) | v2_struct_0(A_171))), inference(resolution, [status(thm)], [c_12, c_189])).
% 2.63/1.43  tff(c_199, plain, (![A_172]: ('#skF_4'(A_172)=k1_xboole_0 | ~v8_pre_topc(A_172) | ~v1_compts_1(A_172) | v9_pre_topc(A_172) | ~l1_pre_topc(A_172) | ~v2_pre_topc(A_172) | v2_struct_0(A_172))), inference(resolution, [status(thm)], [c_76, c_194])).
% 2.63/1.43  tff(c_202, plain, ('#skF_4'('#skF_7')=k1_xboole_0 | ~v8_pre_topc('#skF_7') | ~v1_compts_1('#skF_7') | ~l1_pre_topc('#skF_7') | ~v2_pre_topc('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_199, c_44])).
% 2.63/1.43  tff(c_205, plain, ('#skF_4'('#skF_7')=k1_xboole_0 | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_46, c_48, c_202])).
% 2.63/1.43  tff(c_207, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_62, c_205])).
% 2.63/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.63/1.43  
% 2.63/1.43  Inference rules
% 2.63/1.43  ----------------------
% 2.63/1.43  #Ref     : 0
% 2.63/1.43  #Sup     : 29
% 2.63/1.43  #Fact    : 0
% 2.63/1.43  #Define  : 0
% 2.63/1.43  #Split   : 0
% 2.63/1.43  #Chain   : 0
% 2.63/1.43  #Close   : 0
% 2.63/1.43  
% 2.63/1.43  Ordering : KBO
% 2.63/1.43  
% 2.63/1.43  Simplification rules
% 2.63/1.43  ----------------------
% 2.63/1.43  #Subsume      : 15
% 2.63/1.43  #Demod        : 6
% 2.63/1.43  #Tautology    : 5
% 2.63/1.43  #SimpNegUnit  : 2
% 2.63/1.43  #BackRed      : 0
% 2.63/1.43  
% 2.63/1.43  #Partial instantiations: 0
% 2.63/1.43  #Strategies tried      : 1
% 2.63/1.43  
% 2.63/1.43  Timing (in seconds)
% 2.63/1.43  ----------------------
% 2.63/1.43  Preprocessing        : 0.31
% 2.63/1.43  Parsing              : 0.17
% 2.63/1.43  CNF conversion       : 0.03
% 2.63/1.44  Main loop            : 0.28
% 2.63/1.44  Inferencing          : 0.13
% 2.63/1.44  Reduction            : 0.06
% 2.63/1.44  Demodulation         : 0.04
% 2.63/1.44  BG Simplification    : 0.02
% 2.63/1.44  Subsumption          : 0.06
% 2.63/1.44  Abstraction          : 0.01
% 2.63/1.44  MUC search           : 0.00
% 2.63/1.44  Cooper               : 0.00
% 2.63/1.44  Total                : 0.63
% 2.63/1.44  Index Insertion      : 0.00
% 2.63/1.44  Index Deletion       : 0.00
% 2.63/1.44  Index Matching       : 0.00
% 2.63/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
