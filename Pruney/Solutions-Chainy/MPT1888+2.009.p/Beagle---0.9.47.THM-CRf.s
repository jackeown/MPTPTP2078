%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:21 EST 2020

% Result     : Theorem 4.68s
% Output     : CNFRefutation 4.68s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 474 expanded)
%              Number of leaves         :   39 ( 170 expanded)
%              Depth                    :   14
%              Number of atoms          :  254 (1526 expanded)
%              Number of equality atoms :   29 ( 219 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_pre_topc > r2_hidden > r1_xboole_0 > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k6_domain_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_1 > #skF_5 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(v3_tdlat_3,type,(
    v3_tdlat_3: $i > $o )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_166,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v3_tdlat_3(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ( r1_xboole_0(k2_pre_topc(A,k6_domain_1(u1_struct_0(A),B)),k2_pre_topc(A,k6_domain_1(u1_struct_0(A),C)))
                  | k2_pre_topc(A,k6_domain_1(u1_struct_0(A),B)) = k2_pre_topc(A,k6_domain_1(u1_struct_0(A),C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_tex_2)).

tff(f_62,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_98,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_70,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_42,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_52,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_46,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).

tff(f_127,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( r1_xboole_0(B,C)
                  & v3_pre_topc(B,A) )
               => r1_xboole_0(B,k2_pre_topc(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_tsep_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_76,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => k2_pre_topc(A,k2_pre_topc(A,B)) = k2_pre_topc(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',projectivity_k2_pre_topc)).

tff(f_91,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v4_pre_topc(B,A)
             => k2_pre_topc(A,B) = B )
            & ( ( v2_pre_topc(A)
                & k2_pre_topc(A,B) = B )
             => v4_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).

tff(f_111,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( v3_tdlat_3(A)
      <=> ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
             => v3_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_tdlat_3)).

tff(f_146,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v3_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r2_hidden(B,k2_pre_topc(A,k6_domain_1(u1_struct_0(A),C)))
               => k2_pre_topc(A,k6_domain_1(u1_struct_0(A),B)) = k2_pre_topc(A,k6_domain_1(u1_struct_0(A),C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_tex_2)).

tff(c_50,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_18,plain,(
    ! [A_16] :
      ( l1_struct_0(A_16)
      | ~ l1_pre_topc(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_46,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_91,plain,(
    ! [A_65,B_66] :
      ( k6_domain_1(A_65,B_66) = k1_tarski(B_66)
      | ~ m1_subset_1(B_66,A_65)
      | v1_xboole_0(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_102,plain,
    ( k6_domain_1(u1_struct_0('#skF_3'),'#skF_5') = k1_tarski('#skF_5')
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_46,c_91])).

tff(c_104,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_102])).

tff(c_20,plain,(
    ! [A_17] :
      ( ~ v1_xboole_0(u1_struct_0(A_17))
      | ~ l1_struct_0(A_17)
      | v2_struct_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_107,plain,
    ( ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_104,c_20])).

tff(c_110,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_107])).

tff(c_113,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_110])).

tff(c_117,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_113])).

tff(c_119,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_102])).

tff(c_48,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_103,plain,
    ( k6_domain_1(u1_struct_0('#skF_3'),'#skF_4') = k1_tarski('#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_48,c_91])).

tff(c_131,plain,(
    k6_domain_1(u1_struct_0('#skF_3'),'#skF_4') = k1_tarski('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_119,c_103])).

tff(c_118,plain,(
    k6_domain_1(u1_struct_0('#skF_3'),'#skF_5') = k1_tarski('#skF_5') ),
    inference(splitRight,[status(thm)],[c_102])).

tff(c_42,plain,(
    k2_pre_topc('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),'#skF_5')) != k2_pre_topc('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),'#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_126,plain,(
    k2_pre_topc('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),'#skF_4')) != k2_pre_topc('#skF_3',k1_tarski('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_42])).

tff(c_136,plain,(
    k2_pre_topc('#skF_3',k1_tarski('#skF_5')) != k2_pre_topc('#skF_3',k1_tarski('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_126])).

tff(c_75,plain,(
    ! [A_55,B_56] :
      ( r1_xboole_0(k1_tarski(A_55),B_56)
      | r2_hidden(A_55,B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_6,plain,(
    ! [B_6,A_5] :
      ( r1_xboole_0(B_6,A_5)
      | ~ r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_78,plain,(
    ! [B_56,A_55] :
      ( r1_xboole_0(B_56,k1_tarski(A_55))
      | r2_hidden(A_55,B_56) ) ),
    inference(resolution,[status(thm)],[c_75,c_6])).

tff(c_14,plain,(
    ! [A_12,B_13] :
      ( r2_hidden(A_12,B_13)
      | v1_xboole_0(B_13)
      | ~ m1_subset_1(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_54,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_12,plain,(
    ! [A_10,B_11] :
      ( m1_subset_1(k1_tarski(A_10),k1_zfmisc_1(B_11))
      | ~ r2_hidden(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_238,plain,(
    ! [B_83,A_84,C_85] :
      ( r1_xboole_0(B_83,k2_pre_topc(A_84,C_85))
      | ~ v3_pre_topc(B_83,A_84)
      | ~ r1_xboole_0(B_83,C_85)
      | ~ m1_subset_1(C_85,k1_zfmisc_1(u1_struct_0(A_84)))
      | ~ m1_subset_1(B_83,k1_zfmisc_1(u1_struct_0(A_84)))
      | ~ l1_pre_topc(A_84)
      | ~ v2_pre_topc(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_532,plain,(
    ! [B_122,A_123,A_124] :
      ( r1_xboole_0(B_122,k2_pre_topc(A_123,k1_tarski(A_124)))
      | ~ v3_pre_topc(B_122,A_123)
      | ~ r1_xboole_0(B_122,k1_tarski(A_124))
      | ~ m1_subset_1(B_122,k1_zfmisc_1(u1_struct_0(A_123)))
      | ~ l1_pre_topc(A_123)
      | ~ v2_pre_topc(A_123)
      | ~ r2_hidden(A_124,u1_struct_0(A_123)) ) ),
    inference(resolution,[status(thm)],[c_12,c_238])).

tff(c_44,plain,(
    ~ r1_xboole_0(k2_pre_topc('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),'#skF_4')),k2_pre_topc('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),'#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_125,plain,(
    ~ r1_xboole_0(k2_pre_topc('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),'#skF_4')),k2_pre_topc('#skF_3',k1_tarski('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_44])).

tff(c_137,plain,(
    ~ r1_xboole_0(k2_pre_topc('#skF_3',k1_tarski('#skF_4')),k2_pre_topc('#skF_3',k1_tarski('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_125])).

tff(c_535,plain,
    ( ~ v3_pre_topc(k2_pre_topc('#skF_3',k1_tarski('#skF_4')),'#skF_3')
    | ~ r1_xboole_0(k2_pre_topc('#skF_3',k1_tarski('#skF_4')),k1_tarski('#skF_5'))
    | ~ m1_subset_1(k2_pre_topc('#skF_3',k1_tarski('#skF_4')),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | ~ r2_hidden('#skF_5',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_532,c_137])).

tff(c_540,plain,
    ( ~ v3_pre_topc(k2_pre_topc('#skF_3',k1_tarski('#skF_4')),'#skF_3')
    | ~ r1_xboole_0(k2_pre_topc('#skF_3',k1_tarski('#skF_4')),k1_tarski('#skF_5'))
    | ~ m1_subset_1(k2_pre_topc('#skF_3',k1_tarski('#skF_4')),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ r2_hidden('#skF_5',u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_50,c_535])).

tff(c_542,plain,(
    ~ r2_hidden('#skF_5',u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_540])).

tff(c_545,plain,
    ( v1_xboole_0(u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_14,c_542])).

tff(c_548,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_545])).

tff(c_550,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_119,c_548])).

tff(c_552,plain,(
    r2_hidden('#skF_5',u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_540])).

tff(c_16,plain,(
    ! [A_14,B_15] :
      ( m1_subset_1(k2_pre_topc(A_14,B_15),k1_zfmisc_1(u1_struct_0(A_14)))
      | ~ m1_subset_1(B_15,k1_zfmisc_1(u1_struct_0(A_14)))
      | ~ l1_pre_topc(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_166,plain,(
    ! [A_74,B_75] :
      ( k2_pre_topc(A_74,k2_pre_topc(A_74,B_75)) = k2_pre_topc(A_74,B_75)
      | ~ m1_subset_1(B_75,k1_zfmisc_1(u1_struct_0(A_74)))
      | ~ l1_pre_topc(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_176,plain,(
    ! [A_74,A_10] :
      ( k2_pre_topc(A_74,k2_pre_topc(A_74,k1_tarski(A_10))) = k2_pre_topc(A_74,k1_tarski(A_10))
      | ~ l1_pre_topc(A_74)
      | ~ r2_hidden(A_10,u1_struct_0(A_74)) ) ),
    inference(resolution,[status(thm)],[c_12,c_166])).

tff(c_52,plain,(
    v3_tdlat_3('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_177,plain,(
    ! [B_76,A_77] :
      ( v4_pre_topc(B_76,A_77)
      | k2_pre_topc(A_77,B_76) != B_76
      | ~ v2_pre_topc(A_77)
      | ~ m1_subset_1(B_76,k1_zfmisc_1(u1_struct_0(A_77)))
      | ~ l1_pre_topc(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_409,plain,(
    ! [A_111,B_112] :
      ( v4_pre_topc(k2_pre_topc(A_111,B_112),A_111)
      | k2_pre_topc(A_111,k2_pre_topc(A_111,B_112)) != k2_pre_topc(A_111,B_112)
      | ~ v2_pre_topc(A_111)
      | ~ m1_subset_1(B_112,k1_zfmisc_1(u1_struct_0(A_111)))
      | ~ l1_pre_topc(A_111) ) ),
    inference(resolution,[status(thm)],[c_16,c_177])).

tff(c_520,plain,(
    ! [A_118,A_119] :
      ( v4_pre_topc(k2_pre_topc(A_118,k1_tarski(A_119)),A_118)
      | k2_pre_topc(A_118,k2_pre_topc(A_118,k1_tarski(A_119))) != k2_pre_topc(A_118,k1_tarski(A_119))
      | ~ v2_pre_topc(A_118)
      | ~ l1_pre_topc(A_118)
      | ~ r2_hidden(A_119,u1_struct_0(A_118)) ) ),
    inference(resolution,[status(thm)],[c_12,c_409])).

tff(c_191,plain,(
    ! [B_78,A_79] :
      ( v3_pre_topc(B_78,A_79)
      | ~ v4_pre_topc(B_78,A_79)
      | ~ m1_subset_1(B_78,k1_zfmisc_1(u1_struct_0(A_79)))
      | ~ v3_tdlat_3(A_79)
      | ~ l1_pre_topc(A_79)
      | ~ v2_pre_topc(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_202,plain,(
    ! [A_14,B_15] :
      ( v3_pre_topc(k2_pre_topc(A_14,B_15),A_14)
      | ~ v4_pre_topc(k2_pre_topc(A_14,B_15),A_14)
      | ~ v3_tdlat_3(A_14)
      | ~ v2_pre_topc(A_14)
      | ~ m1_subset_1(B_15,k1_zfmisc_1(u1_struct_0(A_14)))
      | ~ l1_pre_topc(A_14) ) ),
    inference(resolution,[status(thm)],[c_16,c_191])).

tff(c_1659,plain,(
    ! [A_198,A_199] :
      ( v3_pre_topc(k2_pre_topc(A_198,k1_tarski(A_199)),A_198)
      | ~ v3_tdlat_3(A_198)
      | ~ m1_subset_1(k1_tarski(A_199),k1_zfmisc_1(u1_struct_0(A_198)))
      | k2_pre_topc(A_198,k2_pre_topc(A_198,k1_tarski(A_199))) != k2_pre_topc(A_198,k1_tarski(A_199))
      | ~ v2_pre_topc(A_198)
      | ~ l1_pre_topc(A_198)
      | ~ r2_hidden(A_199,u1_struct_0(A_198)) ) ),
    inference(resolution,[status(thm)],[c_520,c_202])).

tff(c_1682,plain,(
    ! [A_200,A_201] :
      ( v3_pre_topc(k2_pre_topc(A_200,k1_tarski(A_201)),A_200)
      | ~ v3_tdlat_3(A_200)
      | k2_pre_topc(A_200,k2_pre_topc(A_200,k1_tarski(A_201))) != k2_pre_topc(A_200,k1_tarski(A_201))
      | ~ v2_pre_topc(A_200)
      | ~ l1_pre_topc(A_200)
      | ~ r2_hidden(A_201,u1_struct_0(A_200)) ) ),
    inference(resolution,[status(thm)],[c_12,c_1659])).

tff(c_559,plain,(
    ! [A_125,A_126,B_127] :
      ( r1_xboole_0(k2_pre_topc(A_125,k1_tarski(A_126)),B_127)
      | ~ v3_pre_topc(B_127,A_125)
      | ~ r1_xboole_0(B_127,k1_tarski(A_126))
      | ~ m1_subset_1(B_127,k1_zfmisc_1(u1_struct_0(A_125)))
      | ~ l1_pre_topc(A_125)
      | ~ v2_pre_topc(A_125)
      | ~ r2_hidden(A_126,u1_struct_0(A_125)) ) ),
    inference(resolution,[status(thm)],[c_532,c_6])).

tff(c_562,plain,
    ( ~ v3_pre_topc(k2_pre_topc('#skF_3',k1_tarski('#skF_5')),'#skF_3')
    | ~ r1_xboole_0(k2_pre_topc('#skF_3',k1_tarski('#skF_5')),k1_tarski('#skF_4'))
    | ~ m1_subset_1(k2_pre_topc('#skF_3',k1_tarski('#skF_5')),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | ~ r2_hidden('#skF_4',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_559,c_137])).

tff(c_567,plain,
    ( ~ v3_pre_topc(k2_pre_topc('#skF_3',k1_tarski('#skF_5')),'#skF_3')
    | ~ r1_xboole_0(k2_pre_topc('#skF_3',k1_tarski('#skF_5')),k1_tarski('#skF_4'))
    | ~ m1_subset_1(k2_pre_topc('#skF_3',k1_tarski('#skF_5')),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ r2_hidden('#skF_4',u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_50,c_562])).

tff(c_569,plain,(
    ~ r2_hidden('#skF_4',u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_567])).

tff(c_572,plain,
    ( v1_xboole_0(u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_14,c_569])).

tff(c_575,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_572])).

tff(c_577,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_119,c_575])).

tff(c_578,plain,
    ( ~ m1_subset_1(k2_pre_topc('#skF_3',k1_tarski('#skF_5')),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ r1_xboole_0(k2_pre_topc('#skF_3',k1_tarski('#skF_5')),k1_tarski('#skF_4'))
    | ~ v3_pre_topc(k2_pre_topc('#skF_3',k1_tarski('#skF_5')),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_567])).

tff(c_621,plain,(
    ~ v3_pre_topc(k2_pre_topc('#skF_3',k1_tarski('#skF_5')),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_578])).

tff(c_1685,plain,
    ( ~ v3_tdlat_3('#skF_3')
    | k2_pre_topc('#skF_3',k2_pre_topc('#skF_3',k1_tarski('#skF_5'))) != k2_pre_topc('#skF_3',k1_tarski('#skF_5'))
    | ~ v2_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ r2_hidden('#skF_5',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_1682,c_621])).

tff(c_1700,plain,(
    k2_pre_topc('#skF_3',k2_pre_topc('#skF_3',k1_tarski('#skF_5'))) != k2_pre_topc('#skF_3',k1_tarski('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_552,c_50,c_54,c_52,c_1685])).

tff(c_1706,plain,
    ( ~ l1_pre_topc('#skF_3')
    | ~ r2_hidden('#skF_5',u1_struct_0('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_176,c_1700])).

tff(c_1710,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_552,c_50,c_1706])).

tff(c_1711,plain,
    ( ~ r1_xboole_0(k2_pre_topc('#skF_3',k1_tarski('#skF_5')),k1_tarski('#skF_4'))
    | ~ m1_subset_1(k2_pre_topc('#skF_3',k1_tarski('#skF_5')),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_578])).

tff(c_1726,plain,(
    ~ m1_subset_1(k2_pre_topc('#skF_3',k1_tarski('#skF_5')),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_1711])).

tff(c_1729,plain,
    ( ~ m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_16,c_1726])).

tff(c_1732,plain,(
    ~ m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_1729])).

tff(c_1736,plain,(
    ~ r2_hidden('#skF_5',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_12,c_1732])).

tff(c_1740,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_552,c_1736])).

tff(c_1741,plain,(
    ~ r1_xboole_0(k2_pre_topc('#skF_3',k1_tarski('#skF_5')),k1_tarski('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_1711])).

tff(c_1752,plain,(
    r2_hidden('#skF_4',k2_pre_topc('#skF_3',k1_tarski('#skF_5'))) ),
    inference(resolution,[status(thm)],[c_78,c_1741])).

tff(c_283,plain,(
    ! [A_96,C_97,B_98] :
      ( k2_pre_topc(A_96,k6_domain_1(u1_struct_0(A_96),C_97)) = k2_pre_topc(A_96,k6_domain_1(u1_struct_0(A_96),B_98))
      | ~ r2_hidden(B_98,k2_pre_topc(A_96,k6_domain_1(u1_struct_0(A_96),C_97)))
      | ~ m1_subset_1(C_97,u1_struct_0(A_96))
      | ~ m1_subset_1(B_98,u1_struct_0(A_96))
      | ~ l1_pre_topc(A_96)
      | ~ v3_tdlat_3(A_96)
      | ~ v2_pre_topc(A_96)
      | v2_struct_0(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_289,plain,(
    ! [B_98] :
      ( k2_pre_topc('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),B_98)) = k2_pre_topc('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),'#skF_5'))
      | ~ r2_hidden(B_98,k2_pre_topc('#skF_3',k1_tarski('#skF_5')))
      | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_98,u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v3_tdlat_3('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_118,c_283])).

tff(c_302,plain,(
    ! [B_98] :
      ( k2_pre_topc('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),B_98)) = k2_pre_topc('#skF_3',k1_tarski('#skF_5'))
      | ~ r2_hidden(B_98,k2_pre_topc('#skF_3',k1_tarski('#skF_5')))
      | ~ m1_subset_1(B_98,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_46,c_118,c_289])).

tff(c_303,plain,(
    ! [B_98] :
      ( k2_pre_topc('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),B_98)) = k2_pre_topc('#skF_3',k1_tarski('#skF_5'))
      | ~ r2_hidden(B_98,k2_pre_topc('#skF_3',k1_tarski('#skF_5')))
      | ~ m1_subset_1(B_98,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_302])).

tff(c_1755,plain,
    ( k2_pre_topc('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),'#skF_4')) = k2_pre_topc('#skF_3',k1_tarski('#skF_5'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_1752,c_303])).

tff(c_1761,plain,(
    k2_pre_topc('#skF_3',k1_tarski('#skF_5')) = k2_pre_topc('#skF_3',k1_tarski('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_131,c_1755])).

tff(c_1763,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_136,c_1761])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:02:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.68/1.95  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.68/1.96  
% 4.68/1.96  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.68/1.96  %$ v4_pre_topc > v3_pre_topc > r2_hidden > r1_xboole_0 > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k6_domain_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_1 > #skF_5 > #skF_3 > #skF_4
% 4.68/1.96  
% 4.68/1.96  %Foreground sorts:
% 4.68/1.96  
% 4.68/1.96  
% 4.68/1.96  %Background operators:
% 4.68/1.96  
% 4.68/1.96  
% 4.68/1.96  %Foreground operators:
% 4.68/1.96  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.68/1.96  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 4.68/1.96  tff('#skF_2', type, '#skF_2': $i > $i).
% 4.68/1.96  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.68/1.96  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.68/1.96  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.68/1.96  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.68/1.96  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.68/1.96  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 4.68/1.96  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.68/1.96  tff('#skF_5', type, '#skF_5': $i).
% 4.68/1.96  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.68/1.96  tff('#skF_3', type, '#skF_3': $i).
% 4.68/1.96  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.68/1.96  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 4.68/1.96  tff(v3_tdlat_3, type, v3_tdlat_3: $i > $o).
% 4.68/1.96  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 4.68/1.96  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.68/1.96  tff('#skF_4', type, '#skF_4': $i).
% 4.68/1.96  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.68/1.96  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.68/1.96  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.68/1.96  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.68/1.96  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 4.68/1.96  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.68/1.96  
% 4.68/1.98  tff(f_166, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_xboole_0(k2_pre_topc(A, k6_domain_1(u1_struct_0(A), B)), k2_pre_topc(A, k6_domain_1(u1_struct_0(A), C))) | (k2_pre_topc(A, k6_domain_1(u1_struct_0(A), B)) = k2_pre_topc(A, k6_domain_1(u1_struct_0(A), C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_tex_2)).
% 4.68/1.98  tff(f_62, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 4.68/1.98  tff(f_98, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 4.68/1.98  tff(f_70, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 4.68/1.98  tff(f_42, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 4.68/1.98  tff(f_35, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 4.68/1.98  tff(f_52, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 4.68/1.98  tff(f_46, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_subset_1)).
% 4.68/1.98  tff(f_127, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r1_xboole_0(B, C) & v3_pre_topc(B, A)) => r1_xboole_0(B, k2_pre_topc(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_tsep_1)).
% 4.68/1.98  tff(f_58, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 4.68/1.98  tff(f_76, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (k2_pre_topc(A, k2_pre_topc(A, B)) = k2_pre_topc(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', projectivity_k2_pre_topc)).
% 4.68/1.98  tff(f_91, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 4.68/1.98  tff(f_111, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (v3_tdlat_3(A) <=> (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => v3_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_tdlat_3)).
% 4.68/1.98  tff(f_146, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(B, k2_pre_topc(A, k6_domain_1(u1_struct_0(A), C))) => (k2_pre_topc(A, k6_domain_1(u1_struct_0(A), B)) = k2_pre_topc(A, k6_domain_1(u1_struct_0(A), C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_tex_2)).
% 4.68/1.98  tff(c_50, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_166])).
% 4.68/1.98  tff(c_18, plain, (![A_16]: (l1_struct_0(A_16) | ~l1_pre_topc(A_16))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.68/1.98  tff(c_56, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_166])).
% 4.68/1.98  tff(c_46, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_166])).
% 4.68/1.98  tff(c_91, plain, (![A_65, B_66]: (k6_domain_1(A_65, B_66)=k1_tarski(B_66) | ~m1_subset_1(B_66, A_65) | v1_xboole_0(A_65))), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.68/1.98  tff(c_102, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_5')=k1_tarski('#skF_5') | v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_46, c_91])).
% 4.68/1.98  tff(c_104, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_102])).
% 4.68/1.98  tff(c_20, plain, (![A_17]: (~v1_xboole_0(u1_struct_0(A_17)) | ~l1_struct_0(A_17) | v2_struct_0(A_17))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.68/1.98  tff(c_107, plain, (~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_104, c_20])).
% 4.68/1.98  tff(c_110, plain, (~l1_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_56, c_107])).
% 4.68/1.98  tff(c_113, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_18, c_110])).
% 4.68/1.98  tff(c_117, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_113])).
% 4.68/1.98  tff(c_119, plain, (~v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_102])).
% 4.68/1.98  tff(c_48, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_166])).
% 4.68/1.98  tff(c_103, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')=k1_tarski('#skF_4') | v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_48, c_91])).
% 4.68/1.98  tff(c_131, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')=k1_tarski('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_119, c_103])).
% 4.68/1.98  tff(c_118, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_5')=k1_tarski('#skF_5')), inference(splitRight, [status(thm)], [c_102])).
% 4.68/1.98  tff(c_42, plain, (k2_pre_topc('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), '#skF_5'))!=k2_pre_topc('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_166])).
% 4.68/1.98  tff(c_126, plain, (k2_pre_topc('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), '#skF_4'))!=k2_pre_topc('#skF_3', k1_tarski('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_118, c_42])).
% 4.68/1.98  tff(c_136, plain, (k2_pre_topc('#skF_3', k1_tarski('#skF_5'))!=k2_pre_topc('#skF_3', k1_tarski('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_131, c_126])).
% 4.68/1.98  tff(c_75, plain, (![A_55, B_56]: (r1_xboole_0(k1_tarski(A_55), B_56) | r2_hidden(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.68/1.98  tff(c_6, plain, (![B_6, A_5]: (r1_xboole_0(B_6, A_5) | ~r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.68/1.98  tff(c_78, plain, (![B_56, A_55]: (r1_xboole_0(B_56, k1_tarski(A_55)) | r2_hidden(A_55, B_56))), inference(resolution, [status(thm)], [c_75, c_6])).
% 4.68/1.98  tff(c_14, plain, (![A_12, B_13]: (r2_hidden(A_12, B_13) | v1_xboole_0(B_13) | ~m1_subset_1(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.68/1.98  tff(c_54, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_166])).
% 4.68/1.98  tff(c_12, plain, (![A_10, B_11]: (m1_subset_1(k1_tarski(A_10), k1_zfmisc_1(B_11)) | ~r2_hidden(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.68/1.98  tff(c_238, plain, (![B_83, A_84, C_85]: (r1_xboole_0(B_83, k2_pre_topc(A_84, C_85)) | ~v3_pre_topc(B_83, A_84) | ~r1_xboole_0(B_83, C_85) | ~m1_subset_1(C_85, k1_zfmisc_1(u1_struct_0(A_84))) | ~m1_subset_1(B_83, k1_zfmisc_1(u1_struct_0(A_84))) | ~l1_pre_topc(A_84) | ~v2_pre_topc(A_84))), inference(cnfTransformation, [status(thm)], [f_127])).
% 4.68/1.98  tff(c_532, plain, (![B_122, A_123, A_124]: (r1_xboole_0(B_122, k2_pre_topc(A_123, k1_tarski(A_124))) | ~v3_pre_topc(B_122, A_123) | ~r1_xboole_0(B_122, k1_tarski(A_124)) | ~m1_subset_1(B_122, k1_zfmisc_1(u1_struct_0(A_123))) | ~l1_pre_topc(A_123) | ~v2_pre_topc(A_123) | ~r2_hidden(A_124, u1_struct_0(A_123)))), inference(resolution, [status(thm)], [c_12, c_238])).
% 4.68/1.98  tff(c_44, plain, (~r1_xboole_0(k2_pre_topc('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')), k2_pre_topc('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_166])).
% 4.68/1.98  tff(c_125, plain, (~r1_xboole_0(k2_pre_topc('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')), k2_pre_topc('#skF_3', k1_tarski('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_118, c_44])).
% 4.68/1.98  tff(c_137, plain, (~r1_xboole_0(k2_pre_topc('#skF_3', k1_tarski('#skF_4')), k2_pre_topc('#skF_3', k1_tarski('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_131, c_125])).
% 4.68/1.98  tff(c_535, plain, (~v3_pre_topc(k2_pre_topc('#skF_3', k1_tarski('#skF_4')), '#skF_3') | ~r1_xboole_0(k2_pre_topc('#skF_3', k1_tarski('#skF_4')), k1_tarski('#skF_5')) | ~m1_subset_1(k2_pre_topc('#skF_3', k1_tarski('#skF_4')), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | ~r2_hidden('#skF_5', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_532, c_137])).
% 4.68/1.98  tff(c_540, plain, (~v3_pre_topc(k2_pre_topc('#skF_3', k1_tarski('#skF_4')), '#skF_3') | ~r1_xboole_0(k2_pre_topc('#skF_3', k1_tarski('#skF_4')), k1_tarski('#skF_5')) | ~m1_subset_1(k2_pre_topc('#skF_3', k1_tarski('#skF_4')), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~r2_hidden('#skF_5', u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_50, c_535])).
% 4.68/1.98  tff(c_542, plain, (~r2_hidden('#skF_5', u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_540])).
% 4.68/1.98  tff(c_545, plain, (v1_xboole_0(u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_14, c_542])).
% 4.68/1.98  tff(c_548, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_545])).
% 4.68/1.98  tff(c_550, plain, $false, inference(negUnitSimplification, [status(thm)], [c_119, c_548])).
% 4.68/1.98  tff(c_552, plain, (r2_hidden('#skF_5', u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_540])).
% 4.68/1.98  tff(c_16, plain, (![A_14, B_15]: (m1_subset_1(k2_pre_topc(A_14, B_15), k1_zfmisc_1(u1_struct_0(A_14))) | ~m1_subset_1(B_15, k1_zfmisc_1(u1_struct_0(A_14))) | ~l1_pre_topc(A_14))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.68/1.98  tff(c_166, plain, (![A_74, B_75]: (k2_pre_topc(A_74, k2_pre_topc(A_74, B_75))=k2_pre_topc(A_74, B_75) | ~m1_subset_1(B_75, k1_zfmisc_1(u1_struct_0(A_74))) | ~l1_pre_topc(A_74))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.68/1.98  tff(c_176, plain, (![A_74, A_10]: (k2_pre_topc(A_74, k2_pre_topc(A_74, k1_tarski(A_10)))=k2_pre_topc(A_74, k1_tarski(A_10)) | ~l1_pre_topc(A_74) | ~r2_hidden(A_10, u1_struct_0(A_74)))), inference(resolution, [status(thm)], [c_12, c_166])).
% 4.68/1.98  tff(c_52, plain, (v3_tdlat_3('#skF_3')), inference(cnfTransformation, [status(thm)], [f_166])).
% 4.68/1.98  tff(c_177, plain, (![B_76, A_77]: (v4_pre_topc(B_76, A_77) | k2_pre_topc(A_77, B_76)!=B_76 | ~v2_pre_topc(A_77) | ~m1_subset_1(B_76, k1_zfmisc_1(u1_struct_0(A_77))) | ~l1_pre_topc(A_77))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.68/1.98  tff(c_409, plain, (![A_111, B_112]: (v4_pre_topc(k2_pre_topc(A_111, B_112), A_111) | k2_pre_topc(A_111, k2_pre_topc(A_111, B_112))!=k2_pre_topc(A_111, B_112) | ~v2_pre_topc(A_111) | ~m1_subset_1(B_112, k1_zfmisc_1(u1_struct_0(A_111))) | ~l1_pre_topc(A_111))), inference(resolution, [status(thm)], [c_16, c_177])).
% 4.68/1.98  tff(c_520, plain, (![A_118, A_119]: (v4_pre_topc(k2_pre_topc(A_118, k1_tarski(A_119)), A_118) | k2_pre_topc(A_118, k2_pre_topc(A_118, k1_tarski(A_119)))!=k2_pre_topc(A_118, k1_tarski(A_119)) | ~v2_pre_topc(A_118) | ~l1_pre_topc(A_118) | ~r2_hidden(A_119, u1_struct_0(A_118)))), inference(resolution, [status(thm)], [c_12, c_409])).
% 4.68/1.98  tff(c_191, plain, (![B_78, A_79]: (v3_pre_topc(B_78, A_79) | ~v4_pre_topc(B_78, A_79) | ~m1_subset_1(B_78, k1_zfmisc_1(u1_struct_0(A_79))) | ~v3_tdlat_3(A_79) | ~l1_pre_topc(A_79) | ~v2_pre_topc(A_79))), inference(cnfTransformation, [status(thm)], [f_111])).
% 4.68/1.98  tff(c_202, plain, (![A_14, B_15]: (v3_pre_topc(k2_pre_topc(A_14, B_15), A_14) | ~v4_pre_topc(k2_pre_topc(A_14, B_15), A_14) | ~v3_tdlat_3(A_14) | ~v2_pre_topc(A_14) | ~m1_subset_1(B_15, k1_zfmisc_1(u1_struct_0(A_14))) | ~l1_pre_topc(A_14))), inference(resolution, [status(thm)], [c_16, c_191])).
% 4.68/1.98  tff(c_1659, plain, (![A_198, A_199]: (v3_pre_topc(k2_pre_topc(A_198, k1_tarski(A_199)), A_198) | ~v3_tdlat_3(A_198) | ~m1_subset_1(k1_tarski(A_199), k1_zfmisc_1(u1_struct_0(A_198))) | k2_pre_topc(A_198, k2_pre_topc(A_198, k1_tarski(A_199)))!=k2_pre_topc(A_198, k1_tarski(A_199)) | ~v2_pre_topc(A_198) | ~l1_pre_topc(A_198) | ~r2_hidden(A_199, u1_struct_0(A_198)))), inference(resolution, [status(thm)], [c_520, c_202])).
% 4.68/1.98  tff(c_1682, plain, (![A_200, A_201]: (v3_pre_topc(k2_pre_topc(A_200, k1_tarski(A_201)), A_200) | ~v3_tdlat_3(A_200) | k2_pre_topc(A_200, k2_pre_topc(A_200, k1_tarski(A_201)))!=k2_pre_topc(A_200, k1_tarski(A_201)) | ~v2_pre_topc(A_200) | ~l1_pre_topc(A_200) | ~r2_hidden(A_201, u1_struct_0(A_200)))), inference(resolution, [status(thm)], [c_12, c_1659])).
% 4.68/1.98  tff(c_559, plain, (![A_125, A_126, B_127]: (r1_xboole_0(k2_pre_topc(A_125, k1_tarski(A_126)), B_127) | ~v3_pre_topc(B_127, A_125) | ~r1_xboole_0(B_127, k1_tarski(A_126)) | ~m1_subset_1(B_127, k1_zfmisc_1(u1_struct_0(A_125))) | ~l1_pre_topc(A_125) | ~v2_pre_topc(A_125) | ~r2_hidden(A_126, u1_struct_0(A_125)))), inference(resolution, [status(thm)], [c_532, c_6])).
% 4.68/1.98  tff(c_562, plain, (~v3_pre_topc(k2_pre_topc('#skF_3', k1_tarski('#skF_5')), '#skF_3') | ~r1_xboole_0(k2_pre_topc('#skF_3', k1_tarski('#skF_5')), k1_tarski('#skF_4')) | ~m1_subset_1(k2_pre_topc('#skF_3', k1_tarski('#skF_5')), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | ~r2_hidden('#skF_4', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_559, c_137])).
% 4.68/1.98  tff(c_567, plain, (~v3_pre_topc(k2_pre_topc('#skF_3', k1_tarski('#skF_5')), '#skF_3') | ~r1_xboole_0(k2_pre_topc('#skF_3', k1_tarski('#skF_5')), k1_tarski('#skF_4')) | ~m1_subset_1(k2_pre_topc('#skF_3', k1_tarski('#skF_5')), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~r2_hidden('#skF_4', u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_50, c_562])).
% 4.68/1.98  tff(c_569, plain, (~r2_hidden('#skF_4', u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_567])).
% 4.68/1.98  tff(c_572, plain, (v1_xboole_0(u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_14, c_569])).
% 4.68/1.98  tff(c_575, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_572])).
% 4.68/1.98  tff(c_577, plain, $false, inference(negUnitSimplification, [status(thm)], [c_119, c_575])).
% 4.68/1.98  tff(c_578, plain, (~m1_subset_1(k2_pre_topc('#skF_3', k1_tarski('#skF_5')), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~r1_xboole_0(k2_pre_topc('#skF_3', k1_tarski('#skF_5')), k1_tarski('#skF_4')) | ~v3_pre_topc(k2_pre_topc('#skF_3', k1_tarski('#skF_5')), '#skF_3')), inference(splitRight, [status(thm)], [c_567])).
% 4.68/1.98  tff(c_621, plain, (~v3_pre_topc(k2_pre_topc('#skF_3', k1_tarski('#skF_5')), '#skF_3')), inference(splitLeft, [status(thm)], [c_578])).
% 4.68/1.98  tff(c_1685, plain, (~v3_tdlat_3('#skF_3') | k2_pre_topc('#skF_3', k2_pre_topc('#skF_3', k1_tarski('#skF_5')))!=k2_pre_topc('#skF_3', k1_tarski('#skF_5')) | ~v2_pre_topc('#skF_3') | ~l1_pre_topc('#skF_3') | ~r2_hidden('#skF_5', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_1682, c_621])).
% 4.68/1.98  tff(c_1700, plain, (k2_pre_topc('#skF_3', k2_pre_topc('#skF_3', k1_tarski('#skF_5')))!=k2_pre_topc('#skF_3', k1_tarski('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_552, c_50, c_54, c_52, c_1685])).
% 4.68/1.98  tff(c_1706, plain, (~l1_pre_topc('#skF_3') | ~r2_hidden('#skF_5', u1_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_176, c_1700])).
% 4.68/1.98  tff(c_1710, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_552, c_50, c_1706])).
% 4.68/1.98  tff(c_1711, plain, (~r1_xboole_0(k2_pre_topc('#skF_3', k1_tarski('#skF_5')), k1_tarski('#skF_4')) | ~m1_subset_1(k2_pre_topc('#skF_3', k1_tarski('#skF_5')), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(splitRight, [status(thm)], [c_578])).
% 4.68/1.98  tff(c_1726, plain, (~m1_subset_1(k2_pre_topc('#skF_3', k1_tarski('#skF_5')), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(splitLeft, [status(thm)], [c_1711])).
% 4.68/1.98  tff(c_1729, plain, (~m1_subset_1(k1_tarski('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_16, c_1726])).
% 4.68/1.98  tff(c_1732, plain, (~m1_subset_1(k1_tarski('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_1729])).
% 4.68/1.98  tff(c_1736, plain, (~r2_hidden('#skF_5', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_12, c_1732])).
% 4.68/1.98  tff(c_1740, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_552, c_1736])).
% 4.68/1.98  tff(c_1741, plain, (~r1_xboole_0(k2_pre_topc('#skF_3', k1_tarski('#skF_5')), k1_tarski('#skF_4'))), inference(splitRight, [status(thm)], [c_1711])).
% 4.68/1.98  tff(c_1752, plain, (r2_hidden('#skF_4', k2_pre_topc('#skF_3', k1_tarski('#skF_5')))), inference(resolution, [status(thm)], [c_78, c_1741])).
% 4.68/1.98  tff(c_283, plain, (![A_96, C_97, B_98]: (k2_pre_topc(A_96, k6_domain_1(u1_struct_0(A_96), C_97))=k2_pre_topc(A_96, k6_domain_1(u1_struct_0(A_96), B_98)) | ~r2_hidden(B_98, k2_pre_topc(A_96, k6_domain_1(u1_struct_0(A_96), C_97))) | ~m1_subset_1(C_97, u1_struct_0(A_96)) | ~m1_subset_1(B_98, u1_struct_0(A_96)) | ~l1_pre_topc(A_96) | ~v3_tdlat_3(A_96) | ~v2_pre_topc(A_96) | v2_struct_0(A_96))), inference(cnfTransformation, [status(thm)], [f_146])).
% 4.68/1.98  tff(c_289, plain, (![B_98]: (k2_pre_topc('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), B_98))=k2_pre_topc('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), '#skF_5')) | ~r2_hidden(B_98, k2_pre_topc('#skF_3', k1_tarski('#skF_5'))) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_3')) | ~m1_subset_1(B_98, u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v3_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_118, c_283])).
% 4.68/1.98  tff(c_302, plain, (![B_98]: (k2_pre_topc('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), B_98))=k2_pre_topc('#skF_3', k1_tarski('#skF_5')) | ~r2_hidden(B_98, k2_pre_topc('#skF_3', k1_tarski('#skF_5'))) | ~m1_subset_1(B_98, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_46, c_118, c_289])).
% 4.68/1.98  tff(c_303, plain, (![B_98]: (k2_pre_topc('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), B_98))=k2_pre_topc('#skF_3', k1_tarski('#skF_5')) | ~r2_hidden(B_98, k2_pre_topc('#skF_3', k1_tarski('#skF_5'))) | ~m1_subset_1(B_98, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_56, c_302])).
% 4.68/1.98  tff(c_1755, plain, (k2_pre_topc('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), '#skF_4'))=k2_pre_topc('#skF_3', k1_tarski('#skF_5')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_1752, c_303])).
% 4.68/1.98  tff(c_1761, plain, (k2_pre_topc('#skF_3', k1_tarski('#skF_5'))=k2_pre_topc('#skF_3', k1_tarski('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_131, c_1755])).
% 4.68/1.98  tff(c_1763, plain, $false, inference(negUnitSimplification, [status(thm)], [c_136, c_1761])).
% 4.68/1.98  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.68/1.98  
% 4.68/1.98  Inference rules
% 4.68/1.98  ----------------------
% 4.68/1.98  #Ref     : 0
% 4.68/1.98  #Sup     : 434
% 4.68/1.98  #Fact    : 2
% 4.68/1.98  #Define  : 0
% 4.68/1.98  #Split   : 8
% 4.68/1.98  #Chain   : 0
% 4.68/1.98  #Close   : 0
% 4.68/1.98  
% 4.68/1.98  Ordering : KBO
% 4.68/1.98  
% 4.68/1.98  Simplification rules
% 4.68/1.98  ----------------------
% 4.68/1.98  #Subsume      : 50
% 4.68/1.98  #Demod        : 108
% 4.68/1.98  #Tautology    : 143
% 4.68/1.98  #SimpNegUnit  : 16
% 4.68/1.98  #BackRed      : 2
% 4.68/1.98  
% 4.68/1.98  #Partial instantiations: 0
% 4.68/1.98  #Strategies tried      : 1
% 4.68/1.98  
% 4.68/1.98  Timing (in seconds)
% 4.68/1.98  ----------------------
% 4.68/1.98  Preprocessing        : 0.39
% 4.68/1.98  Parsing              : 0.20
% 4.68/1.98  CNF conversion       : 0.03
% 4.68/1.98  Main loop            : 0.77
% 4.68/1.98  Inferencing          : 0.28
% 4.68/1.98  Reduction            : 0.19
% 4.68/1.98  Demodulation         : 0.12
% 4.68/1.98  BG Simplification    : 0.04
% 4.68/1.98  Subsumption          : 0.22
% 4.68/1.98  Abstraction          : 0.04
% 4.68/1.98  MUC search           : 0.00
% 4.68/1.98  Cooper               : 0.00
% 4.68/1.98  Total                : 1.20
% 4.68/1.98  Index Insertion      : 0.00
% 4.68/1.98  Index Deletion       : 0.00
% 4.68/1.98  Index Matching       : 0.00
% 4.68/1.98  BG Taut test         : 0.00
%------------------------------------------------------------------------------
