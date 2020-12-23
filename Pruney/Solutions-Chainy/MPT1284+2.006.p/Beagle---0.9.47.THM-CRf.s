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
% DateTime   : Thu Dec  3 10:22:23 EST 2020

% Result     : Theorem 3.58s
% Output     : CNFRefutation 3.58s
% Verified   : 
% Statistics : Number of formulae       :  141 ( 307 expanded)
%              Number of leaves         :   27 ( 119 expanded)
%              Depth                    :   13
%              Number of atoms          :  320 (1295 expanded)
%              Number of equality atoms :   36 (  52 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_tops_1 > v4_tops_1 > v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v4_tops_1,type,(
    v4_tops_1: ( $i * $i ) > $o )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff(v5_tops_1,type,(
    v5_tops_1: ( $i * $i ) > $o )).

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

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_125,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( l1_pre_topc(B)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(B)))
                   => ( ( ( v4_pre_topc(D,B)
                          & v4_tops_1(D,B) )
                       => v5_tops_1(D,B) )
                      & ( v5_tops_1(C,A)
                       => ( v4_pre_topc(C,A)
                          & v4_tops_1(C,A) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_tops_1)).

tff(f_99,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_78,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v5_tops_1(B,A)
          <=> B = k2_pre_topc(A,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tops_1)).

tff(f_84,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k1_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tops_1)).

tff(f_92,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v4_pre_topc(k2_pre_topc(A,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_tops_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_58,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v4_pre_topc(B,A)
             => k2_pre_topc(A,B) = B )
            & ( ( v2_pre_topc(A)
                & k2_pre_topc(A,B) = B )
             => v4_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).

tff(f_69,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_tops_1(B,A)
          <=> ( r1_tarski(k1_tops_1(A,k2_pre_topc(A,B)),B)
              & r1_tarski(B,k2_pre_topc(A,k1_tops_1(A,B))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_tops_1)).

tff(f_43,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( r1_tarski(B,C)
               => r1_tarski(k2_pre_topc(A,B),k2_pre_topc(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_pre_topc)).

tff(c_44,plain,
    ( v4_pre_topc('#skF_4','#skF_2')
    | ~ v4_tops_1('#skF_3','#skF_1')
    | ~ v4_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_1264,plain,(
    ~ v4_pre_topc('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_36,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_32,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_38,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_46,plain,
    ( ~ v5_tops_1('#skF_4','#skF_2')
    | v5_tops_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_53,plain,(
    ~ v5_tops_1('#skF_4','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_34,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_30,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_983,plain,(
    ! [A_142,B_143] :
      ( r1_tarski(k1_tops_1(A_142,B_143),B_143)
      | ~ m1_subset_1(B_143,k1_zfmisc_1(u1_struct_0(A_142)))
      | ~ l1_pre_topc(A_142) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_987,plain,
    ( r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_983])).

tff(c_993,plain,(
    r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_987])).

tff(c_423,plain,(
    ! [A_91,B_92] :
      ( r1_tarski(k1_tops_1(A_91,B_92),B_92)
      | ~ m1_subset_1(B_92,k1_zfmisc_1(u1_struct_0(A_91)))
      | ~ l1_pre_topc(A_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_427,plain,
    ( r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_423])).

tff(c_433,plain,(
    r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_427])).

tff(c_64,plain,(
    ~ v4_pre_topc('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_50,plain,
    ( v4_pre_topc('#skF_4','#skF_2')
    | v5_tops_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_54,plain,(
    v5_tops_1('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_141,plain,(
    ! [A_52,B_53] :
      ( k2_pre_topc(A_52,k1_tops_1(A_52,B_53)) = B_53
      | ~ v5_tops_1(B_53,A_52)
      | ~ m1_subset_1(B_53,k1_zfmisc_1(u1_struct_0(A_52)))
      | ~ l1_pre_topc(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_145,plain,
    ( k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_3')) = '#skF_3'
    | ~ v5_tops_1('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_141])).

tff(c_151,plain,(
    k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_54,c_145])).

tff(c_110,plain,(
    ! [A_46,B_47] :
      ( m1_subset_1(k1_tops_1(A_46,B_47),k1_zfmisc_1(u1_struct_0(A_46)))
      | ~ m1_subset_1(B_47,k1_zfmisc_1(u1_struct_0(A_46)))
      | ~ l1_pre_topc(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_26,plain,(
    ! [A_21,B_22] :
      ( v4_pre_topc(k2_pre_topc(A_21,B_22),A_21)
      | ~ m1_subset_1(B_22,k1_zfmisc_1(u1_struct_0(A_21)))
      | ~ l1_pre_topc(A_21)
      | ~ v2_pre_topc(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_164,plain,(
    ! [A_54,B_55] :
      ( v4_pre_topc(k2_pre_topc(A_54,k1_tops_1(A_54,B_55)),A_54)
      | ~ v2_pre_topc(A_54)
      | ~ m1_subset_1(B_55,k1_zfmisc_1(u1_struct_0(A_54)))
      | ~ l1_pre_topc(A_54) ) ),
    inference(resolution,[status(thm)],[c_110,c_26])).

tff(c_167,plain,
    ( v4_pre_topc('#skF_3','#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_151,c_164])).

tff(c_169,plain,(
    v4_pre_topc('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_38,c_167])).

tff(c_171,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_169])).

tff(c_173,plain,(
    v4_pre_topc('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_172,plain,
    ( ~ v4_tops_1('#skF_3','#skF_1')
    | v4_pre_topc('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_176,plain,(
    ~ v4_tops_1('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_172])).

tff(c_179,plain,(
    ! [A_56,B_57] :
      ( r1_tarski(k1_tops_1(A_56,B_57),B_57)
      | ~ m1_subset_1(B_57,k1_zfmisc_1(u1_struct_0(A_56)))
      | ~ l1_pre_topc(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_181,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_179])).

tff(c_186,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_181])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_259,plain,(
    ! [A_66,B_67] :
      ( k2_pre_topc(A_66,k1_tops_1(A_66,B_67)) = B_67
      | ~ v5_tops_1(B_67,A_66)
      | ~ m1_subset_1(B_67,k1_zfmisc_1(u1_struct_0(A_66)))
      | ~ l1_pre_topc(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_263,plain,
    ( k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_3')) = '#skF_3'
    | ~ v5_tops_1('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_259])).

tff(c_269,plain,(
    k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_54,c_263])).

tff(c_210,plain,(
    ! [A_60,B_61] :
      ( k2_pre_topc(A_60,B_61) = B_61
      | ~ v4_pre_topc(B_61,A_60)
      | ~ m1_subset_1(B_61,k1_zfmisc_1(u1_struct_0(A_60)))
      | ~ l1_pre_topc(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_213,plain,
    ( k2_pre_topc('#skF_1','#skF_3') = '#skF_3'
    | ~ v4_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_210])).

tff(c_219,plain,(
    k2_pre_topc('#skF_1','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_173,c_213])).

tff(c_402,plain,(
    ! [B_89,A_90] :
      ( v4_tops_1(B_89,A_90)
      | ~ r1_tarski(B_89,k2_pre_topc(A_90,k1_tops_1(A_90,B_89)))
      | ~ r1_tarski(k1_tops_1(A_90,k2_pre_topc(A_90,B_89)),B_89)
      | ~ m1_subset_1(B_89,k1_zfmisc_1(u1_struct_0(A_90)))
      | ~ l1_pre_topc(A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_411,plain,
    ( v4_tops_1('#skF_3','#skF_1')
    | ~ r1_tarski('#skF_3',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_3')))
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_219,c_402])).

tff(c_416,plain,(
    v4_tops_1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_186,c_6,c_269,c_411])).

tff(c_418,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_176,c_416])).

tff(c_420,plain,(
    v4_tops_1('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_172])).

tff(c_42,plain,
    ( v4_tops_1('#skF_4','#skF_2')
    | ~ v4_tops_1('#skF_3','#skF_1')
    | ~ v4_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_422,plain,(
    v4_tops_1('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_420,c_42])).

tff(c_24,plain,(
    ! [A_19,B_20] :
      ( m1_subset_1(k1_tops_1(A_19,B_20),k1_zfmisc_1(u1_struct_0(A_19)))
      | ~ m1_subset_1(B_20,k1_zfmisc_1(u1_struct_0(A_19)))
      | ~ l1_pre_topc(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_419,plain,(
    v4_pre_topc('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_172])).

tff(c_461,plain,(
    ! [A_97,B_98] :
      ( k2_pre_topc(A_97,B_98) = B_98
      | ~ v4_pre_topc(B_98,A_97)
      | ~ m1_subset_1(B_98,k1_zfmisc_1(u1_struct_0(A_97)))
      | ~ l1_pre_topc(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_470,plain,
    ( k2_pre_topc('#skF_2','#skF_4') = '#skF_4'
    | ~ v4_pre_topc('#skF_4','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_461])).

tff(c_477,plain,(
    k2_pre_topc('#skF_2','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_419,c_470])).

tff(c_568,plain,(
    ! [A_115,B_116,C_117] :
      ( r1_tarski(k2_pre_topc(A_115,B_116),k2_pre_topc(A_115,C_117))
      | ~ r1_tarski(B_116,C_117)
      | ~ m1_subset_1(C_117,k1_zfmisc_1(u1_struct_0(A_115)))
      | ~ m1_subset_1(B_116,k1_zfmisc_1(u1_struct_0(A_115)))
      | ~ l1_pre_topc(A_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_582,plain,(
    ! [B_116] :
      ( r1_tarski(k2_pre_topc('#skF_2',B_116),'#skF_4')
      | ~ r1_tarski(B_116,'#skF_4')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(B_116,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_477,c_568])).

tff(c_636,plain,(
    ! [B_121] :
      ( r1_tarski(k2_pre_topc('#skF_2',B_121),'#skF_4')
      | ~ r1_tarski(B_121,'#skF_4')
      | ~ m1_subset_1(B_121,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_582])).

tff(c_640,plain,(
    ! [B_20] :
      ( r1_tarski(k2_pre_topc('#skF_2',k1_tops_1('#skF_2',B_20)),'#skF_4')
      | ~ r1_tarski(k1_tops_1('#skF_2',B_20),'#skF_4')
      | ~ m1_subset_1(B_20,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_24,c_636])).

tff(c_646,plain,(
    ! [B_20] :
      ( r1_tarski(k2_pre_topc('#skF_2',k1_tops_1('#skF_2',B_20)),'#skF_4')
      | ~ r1_tarski(k1_tops_1('#skF_2',B_20),'#skF_4')
      | ~ m1_subset_1(B_20,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_640])).

tff(c_535,plain,(
    ! [B_107,A_108] :
      ( r1_tarski(B_107,k2_pre_topc(A_108,k1_tops_1(A_108,B_107)))
      | ~ v4_tops_1(B_107,A_108)
      | ~ m1_subset_1(B_107,k1_zfmisc_1(u1_struct_0(A_108)))
      | ~ l1_pre_topc(A_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_876,plain,(
    ! [A_138,B_139] :
      ( k2_pre_topc(A_138,k1_tops_1(A_138,B_139)) = B_139
      | ~ r1_tarski(k2_pre_topc(A_138,k1_tops_1(A_138,B_139)),B_139)
      | ~ v4_tops_1(B_139,A_138)
      | ~ m1_subset_1(B_139,k1_zfmisc_1(u1_struct_0(A_138)))
      | ~ l1_pre_topc(A_138) ) ),
    inference(resolution,[status(thm)],[c_535,c_2])).

tff(c_888,plain,
    ( k2_pre_topc('#skF_2',k1_tops_1('#skF_2','#skF_4')) = '#skF_4'
    | ~ v4_tops_1('#skF_4','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_646,c_876])).

tff(c_904,plain,(
    k2_pre_topc('#skF_2',k1_tops_1('#skF_2','#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_433,c_34,c_422,c_888])).

tff(c_20,plain,(
    ! [B_18,A_16] :
      ( v5_tops_1(B_18,A_16)
      | k2_pre_topc(A_16,k1_tops_1(A_16,B_18)) != B_18
      | ~ m1_subset_1(B_18,k1_zfmisc_1(u1_struct_0(A_16)))
      | ~ l1_pre_topc(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_943,plain,
    ( v5_tops_1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_904,c_20])).

tff(c_968,plain,(
    v5_tops_1('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_943])).

tff(c_970,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_53,c_968])).

tff(c_972,plain,(
    ~ v5_tops_1('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_48,plain,
    ( v4_tops_1('#skF_4','#skF_2')
    | v5_tops_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_973,plain,(
    v4_tops_1('#skF_4','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_972,c_48])).

tff(c_971,plain,(
    v4_pre_topc('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_1002,plain,(
    ! [A_144,B_145] :
      ( k2_pre_topc(A_144,B_145) = B_145
      | ~ v4_pre_topc(B_145,A_144)
      | ~ m1_subset_1(B_145,k1_zfmisc_1(u1_struct_0(A_144)))
      | ~ l1_pre_topc(A_144) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1008,plain,
    ( k2_pre_topc('#skF_2','#skF_4') = '#skF_4'
    | ~ v4_pre_topc('#skF_4','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_1002])).

tff(c_1014,plain,(
    k2_pre_topc('#skF_2','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_971,c_1008])).

tff(c_1094,plain,(
    ! [A_166,B_167,C_168] :
      ( r1_tarski(k2_pre_topc(A_166,B_167),k2_pre_topc(A_166,C_168))
      | ~ r1_tarski(B_167,C_168)
      | ~ m1_subset_1(C_168,k1_zfmisc_1(u1_struct_0(A_166)))
      | ~ m1_subset_1(B_167,k1_zfmisc_1(u1_struct_0(A_166)))
      | ~ l1_pre_topc(A_166) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1102,plain,(
    ! [B_167] :
      ( r1_tarski(k2_pre_topc('#skF_2',B_167),'#skF_4')
      | ~ r1_tarski(B_167,'#skF_4')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(B_167,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1014,c_1094])).

tff(c_1122,plain,(
    ! [B_170] :
      ( r1_tarski(k2_pre_topc('#skF_2',B_170),'#skF_4')
      | ~ r1_tarski(B_170,'#skF_4')
      | ~ m1_subset_1(B_170,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_1102])).

tff(c_1126,plain,(
    ! [B_20] :
      ( r1_tarski(k2_pre_topc('#skF_2',k1_tops_1('#skF_2',B_20)),'#skF_4')
      | ~ r1_tarski(k1_tops_1('#skF_2',B_20),'#skF_4')
      | ~ m1_subset_1(B_20,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_24,c_1122])).

tff(c_1132,plain,(
    ! [B_20] :
      ( r1_tarski(k2_pre_topc('#skF_2',k1_tops_1('#skF_2',B_20)),'#skF_4')
      | ~ r1_tarski(k1_tops_1('#skF_2',B_20),'#skF_4')
      | ~ m1_subset_1(B_20,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1126])).

tff(c_1089,plain,(
    ! [B_162,A_163] :
      ( r1_tarski(B_162,k2_pre_topc(A_163,k1_tops_1(A_163,B_162)))
      | ~ v4_tops_1(B_162,A_163)
      | ~ m1_subset_1(B_162,k1_zfmisc_1(u1_struct_0(A_163)))
      | ~ l1_pre_topc(A_163) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1185,plain,(
    ! [A_179,B_180] :
      ( k2_pre_topc(A_179,k1_tops_1(A_179,B_180)) = B_180
      | ~ r1_tarski(k2_pre_topc(A_179,k1_tops_1(A_179,B_180)),B_180)
      | ~ v4_tops_1(B_180,A_179)
      | ~ m1_subset_1(B_180,k1_zfmisc_1(u1_struct_0(A_179)))
      | ~ l1_pre_topc(A_179) ) ),
    inference(resolution,[status(thm)],[c_1089,c_2])).

tff(c_1189,plain,
    ( k2_pre_topc('#skF_2',k1_tops_1('#skF_2','#skF_4')) = '#skF_4'
    | ~ v4_tops_1('#skF_4','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_1132,c_1185])).

tff(c_1196,plain,(
    k2_pre_topc('#skF_2',k1_tops_1('#skF_2','#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_993,c_34,c_973,c_1189])).

tff(c_1227,plain,
    ( v5_tops_1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1196,c_20])).

tff(c_1250,plain,(
    v5_tops_1('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_1227])).

tff(c_1252,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_53,c_1250])).

tff(c_1253,plain,(
    v5_tops_1('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_1343,plain,(
    ! [A_195,B_196] :
      ( k2_pre_topc(A_195,k1_tops_1(A_195,B_196)) = B_196
      | ~ v5_tops_1(B_196,A_195)
      | ~ m1_subset_1(B_196,k1_zfmisc_1(u1_struct_0(A_195)))
      | ~ l1_pre_topc(A_195) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1347,plain,
    ( k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_3')) = '#skF_3'
    | ~ v5_tops_1('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_1343])).

tff(c_1353,plain,(
    k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1253,c_1347])).

tff(c_1312,plain,(
    ! [A_189,B_190] :
      ( m1_subset_1(k1_tops_1(A_189,B_190),k1_zfmisc_1(u1_struct_0(A_189)))
      | ~ m1_subset_1(B_190,k1_zfmisc_1(u1_struct_0(A_189)))
      | ~ l1_pre_topc(A_189) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1389,plain,(
    ! [A_199,B_200] :
      ( v4_pre_topc(k2_pre_topc(A_199,k1_tops_1(A_199,B_200)),A_199)
      | ~ v2_pre_topc(A_199)
      | ~ m1_subset_1(B_200,k1_zfmisc_1(u1_struct_0(A_199)))
      | ~ l1_pre_topc(A_199) ) ),
    inference(resolution,[status(thm)],[c_1312,c_26])).

tff(c_1395,plain,
    ( v4_pre_topc('#skF_3','#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1353,c_1389])).

tff(c_1400,plain,(
    v4_pre_topc('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_38,c_1395])).

tff(c_1402,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1264,c_1400])).

tff(c_1404,plain,(
    v4_pre_topc('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_1254,plain,(
    v5_tops_1('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_40,plain,
    ( ~ v5_tops_1('#skF_4','#skF_2')
    | ~ v4_tops_1('#skF_3','#skF_1')
    | ~ v4_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_1406,plain,
    ( ~ v4_tops_1('#skF_3','#skF_1')
    | ~ v4_pre_topc('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1254,c_40])).

tff(c_1407,plain,(
    ~ v4_pre_topc('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1406])).

tff(c_1409,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1404,c_1407])).

tff(c_1410,plain,(
    ~ v4_tops_1('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_1406])).

tff(c_1415,plain,(
    ! [A_201,B_202] :
      ( r1_tarski(k1_tops_1(A_201,B_202),B_202)
      | ~ m1_subset_1(B_202,k1_zfmisc_1(u1_struct_0(A_201)))
      | ~ l1_pre_topc(A_201) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_1417,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_1415])).

tff(c_1422,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1417])).

tff(c_1477,plain,(
    ! [A_211,B_212] :
      ( k2_pre_topc(A_211,k1_tops_1(A_211,B_212)) = B_212
      | ~ v5_tops_1(B_212,A_211)
      | ~ m1_subset_1(B_212,k1_zfmisc_1(u1_struct_0(A_211)))
      | ~ l1_pre_topc(A_211) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1481,plain,
    ( k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_3')) = '#skF_3'
    | ~ v5_tops_1('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_1477])).

tff(c_1487,plain,(
    k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1253,c_1481])).

tff(c_1434,plain,(
    ! [A_203,B_204] :
      ( k2_pre_topc(A_203,B_204) = B_204
      | ~ v4_pre_topc(B_204,A_203)
      | ~ m1_subset_1(B_204,k1_zfmisc_1(u1_struct_0(A_203)))
      | ~ l1_pre_topc(A_203) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1437,plain,
    ( k2_pre_topc('#skF_1','#skF_3') = '#skF_3'
    | ~ v4_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_1434])).

tff(c_1443,plain,(
    k2_pre_topc('#skF_1','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1404,c_1437])).

tff(c_1625,plain,(
    ! [B_229,A_230] :
      ( v4_tops_1(B_229,A_230)
      | ~ r1_tarski(B_229,k2_pre_topc(A_230,k1_tops_1(A_230,B_229)))
      | ~ r1_tarski(k1_tops_1(A_230,k2_pre_topc(A_230,B_229)),B_229)
      | ~ m1_subset_1(B_229,k1_zfmisc_1(u1_struct_0(A_230)))
      | ~ l1_pre_topc(A_230) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1637,plain,
    ( v4_tops_1('#skF_3','#skF_1')
    | ~ r1_tarski('#skF_3',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_3')))
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1443,c_1625])).

tff(c_1644,plain,(
    v4_tops_1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_1422,c_6,c_1487,c_1637])).

tff(c_1646,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1410,c_1644])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:11:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.58/1.55  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.58/1.56  
% 3.58/1.56  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.58/1.57  %$ v5_tops_1 > v4_tops_1 > v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.58/1.57  
% 3.58/1.57  %Foreground sorts:
% 3.58/1.57  
% 3.58/1.57  
% 3.58/1.57  %Background operators:
% 3.58/1.57  
% 3.58/1.57  
% 3.58/1.57  %Foreground operators:
% 3.58/1.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.58/1.57  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.58/1.57  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.58/1.57  tff(v4_tops_1, type, v4_tops_1: ($i * $i) > $o).
% 3.58/1.57  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 3.58/1.57  tff('#skF_2', type, '#skF_2': $i).
% 3.58/1.57  tff('#skF_3', type, '#skF_3': $i).
% 3.58/1.57  tff('#skF_1', type, '#skF_1': $i).
% 3.58/1.57  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.58/1.57  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 3.58/1.57  tff(v5_tops_1, type, v5_tops_1: ($i * $i) > $o).
% 3.58/1.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.58/1.57  tff('#skF_4', type, '#skF_4': $i).
% 3.58/1.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.58/1.57  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.58/1.57  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.58/1.57  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.58/1.57  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.58/1.57  
% 3.58/1.59  tff(f_125, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (l1_pre_topc(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => (((v4_pre_topc(D, B) & v4_tops_1(D, B)) => v5_tops_1(D, B)) & (v5_tops_1(C, A) => (v4_pre_topc(C, A) & v4_tops_1(C, A)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_tops_1)).
% 3.58/1.59  tff(f_99, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tops_1)).
% 3.58/1.59  tff(f_78, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v5_tops_1(B, A) <=> (B = k2_pre_topc(A, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_tops_1)).
% 3.58/1.59  tff(f_84, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k1_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tops_1)).
% 3.58/1.59  tff(f_92, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v4_pre_topc(k2_pre_topc(A, B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_tops_1)).
% 3.58/1.59  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.58/1.59  tff(f_58, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 3.58/1.59  tff(f_69, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_tops_1(B, A) <=> (r1_tarski(k1_tops_1(A, k2_pre_topc(A, B)), B) & r1_tarski(B, k2_pre_topc(A, k1_tops_1(A, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_tops_1)).
% 3.58/1.59  tff(f_43, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(B, C) => r1_tarski(k2_pre_topc(A, B), k2_pre_topc(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_pre_topc)).
% 3.58/1.59  tff(c_44, plain, (v4_pre_topc('#skF_4', '#skF_2') | ~v4_tops_1('#skF_3', '#skF_1') | ~v4_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.58/1.59  tff(c_1264, plain, (~v4_pre_topc('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_44])).
% 3.58/1.59  tff(c_36, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.58/1.59  tff(c_32, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.58/1.59  tff(c_38, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.58/1.59  tff(c_46, plain, (~v5_tops_1('#skF_4', '#skF_2') | v5_tops_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.58/1.59  tff(c_53, plain, (~v5_tops_1('#skF_4', '#skF_2')), inference(splitLeft, [status(thm)], [c_46])).
% 3.58/1.59  tff(c_34, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.58/1.59  tff(c_30, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.58/1.59  tff(c_983, plain, (![A_142, B_143]: (r1_tarski(k1_tops_1(A_142, B_143), B_143) | ~m1_subset_1(B_143, k1_zfmisc_1(u1_struct_0(A_142))) | ~l1_pre_topc(A_142))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.58/1.59  tff(c_987, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_30, c_983])).
% 3.58/1.59  tff(c_993, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_987])).
% 3.58/1.59  tff(c_423, plain, (![A_91, B_92]: (r1_tarski(k1_tops_1(A_91, B_92), B_92) | ~m1_subset_1(B_92, k1_zfmisc_1(u1_struct_0(A_91))) | ~l1_pre_topc(A_91))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.58/1.59  tff(c_427, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_30, c_423])).
% 3.58/1.59  tff(c_433, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_427])).
% 3.58/1.59  tff(c_64, plain, (~v4_pre_topc('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_44])).
% 3.58/1.59  tff(c_50, plain, (v4_pre_topc('#skF_4', '#skF_2') | v5_tops_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.58/1.59  tff(c_54, plain, (v5_tops_1('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_50])).
% 3.58/1.59  tff(c_141, plain, (![A_52, B_53]: (k2_pre_topc(A_52, k1_tops_1(A_52, B_53))=B_53 | ~v5_tops_1(B_53, A_52) | ~m1_subset_1(B_53, k1_zfmisc_1(u1_struct_0(A_52))) | ~l1_pre_topc(A_52))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.58/1.59  tff(c_145, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_3'))='#skF_3' | ~v5_tops_1('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_141])).
% 3.58/1.59  tff(c_151, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_54, c_145])).
% 3.58/1.59  tff(c_110, plain, (![A_46, B_47]: (m1_subset_1(k1_tops_1(A_46, B_47), k1_zfmisc_1(u1_struct_0(A_46))) | ~m1_subset_1(B_47, k1_zfmisc_1(u1_struct_0(A_46))) | ~l1_pre_topc(A_46))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.58/1.59  tff(c_26, plain, (![A_21, B_22]: (v4_pre_topc(k2_pre_topc(A_21, B_22), A_21) | ~m1_subset_1(B_22, k1_zfmisc_1(u1_struct_0(A_21))) | ~l1_pre_topc(A_21) | ~v2_pre_topc(A_21))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.58/1.59  tff(c_164, plain, (![A_54, B_55]: (v4_pre_topc(k2_pre_topc(A_54, k1_tops_1(A_54, B_55)), A_54) | ~v2_pre_topc(A_54) | ~m1_subset_1(B_55, k1_zfmisc_1(u1_struct_0(A_54))) | ~l1_pre_topc(A_54))), inference(resolution, [status(thm)], [c_110, c_26])).
% 3.58/1.59  tff(c_167, plain, (v4_pre_topc('#skF_3', '#skF_1') | ~v2_pre_topc('#skF_1') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_151, c_164])).
% 3.58/1.59  tff(c_169, plain, (v4_pre_topc('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_38, c_167])).
% 3.58/1.59  tff(c_171, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_169])).
% 3.58/1.59  tff(c_173, plain, (v4_pre_topc('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_44])).
% 3.58/1.59  tff(c_172, plain, (~v4_tops_1('#skF_3', '#skF_1') | v4_pre_topc('#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_44])).
% 3.58/1.59  tff(c_176, plain, (~v4_tops_1('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_172])).
% 3.58/1.59  tff(c_179, plain, (![A_56, B_57]: (r1_tarski(k1_tops_1(A_56, B_57), B_57) | ~m1_subset_1(B_57, k1_zfmisc_1(u1_struct_0(A_56))) | ~l1_pre_topc(A_56))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.58/1.59  tff(c_181, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_179])).
% 3.58/1.59  tff(c_186, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_181])).
% 3.58/1.59  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.58/1.59  tff(c_259, plain, (![A_66, B_67]: (k2_pre_topc(A_66, k1_tops_1(A_66, B_67))=B_67 | ~v5_tops_1(B_67, A_66) | ~m1_subset_1(B_67, k1_zfmisc_1(u1_struct_0(A_66))) | ~l1_pre_topc(A_66))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.58/1.59  tff(c_263, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_3'))='#skF_3' | ~v5_tops_1('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_259])).
% 3.58/1.59  tff(c_269, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_54, c_263])).
% 3.58/1.59  tff(c_210, plain, (![A_60, B_61]: (k2_pre_topc(A_60, B_61)=B_61 | ~v4_pre_topc(B_61, A_60) | ~m1_subset_1(B_61, k1_zfmisc_1(u1_struct_0(A_60))) | ~l1_pre_topc(A_60))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.58/1.59  tff(c_213, plain, (k2_pre_topc('#skF_1', '#skF_3')='#skF_3' | ~v4_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_210])).
% 3.58/1.59  tff(c_219, plain, (k2_pre_topc('#skF_1', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_173, c_213])).
% 3.58/1.59  tff(c_402, plain, (![B_89, A_90]: (v4_tops_1(B_89, A_90) | ~r1_tarski(B_89, k2_pre_topc(A_90, k1_tops_1(A_90, B_89))) | ~r1_tarski(k1_tops_1(A_90, k2_pre_topc(A_90, B_89)), B_89) | ~m1_subset_1(B_89, k1_zfmisc_1(u1_struct_0(A_90))) | ~l1_pre_topc(A_90))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.58/1.59  tff(c_411, plain, (v4_tops_1('#skF_3', '#skF_1') | ~r1_tarski('#skF_3', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_3'))) | ~r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_219, c_402])).
% 3.58/1.59  tff(c_416, plain, (v4_tops_1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_186, c_6, c_269, c_411])).
% 3.58/1.59  tff(c_418, plain, $false, inference(negUnitSimplification, [status(thm)], [c_176, c_416])).
% 3.58/1.59  tff(c_420, plain, (v4_tops_1('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_172])).
% 3.58/1.59  tff(c_42, plain, (v4_tops_1('#skF_4', '#skF_2') | ~v4_tops_1('#skF_3', '#skF_1') | ~v4_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.58/1.59  tff(c_422, plain, (v4_tops_1('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_173, c_420, c_42])).
% 3.58/1.59  tff(c_24, plain, (![A_19, B_20]: (m1_subset_1(k1_tops_1(A_19, B_20), k1_zfmisc_1(u1_struct_0(A_19))) | ~m1_subset_1(B_20, k1_zfmisc_1(u1_struct_0(A_19))) | ~l1_pre_topc(A_19))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.58/1.59  tff(c_419, plain, (v4_pre_topc('#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_172])).
% 3.58/1.59  tff(c_461, plain, (![A_97, B_98]: (k2_pre_topc(A_97, B_98)=B_98 | ~v4_pre_topc(B_98, A_97) | ~m1_subset_1(B_98, k1_zfmisc_1(u1_struct_0(A_97))) | ~l1_pre_topc(A_97))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.58/1.59  tff(c_470, plain, (k2_pre_topc('#skF_2', '#skF_4')='#skF_4' | ~v4_pre_topc('#skF_4', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_30, c_461])).
% 3.58/1.59  tff(c_477, plain, (k2_pre_topc('#skF_2', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_419, c_470])).
% 3.58/1.59  tff(c_568, plain, (![A_115, B_116, C_117]: (r1_tarski(k2_pre_topc(A_115, B_116), k2_pre_topc(A_115, C_117)) | ~r1_tarski(B_116, C_117) | ~m1_subset_1(C_117, k1_zfmisc_1(u1_struct_0(A_115))) | ~m1_subset_1(B_116, k1_zfmisc_1(u1_struct_0(A_115))) | ~l1_pre_topc(A_115))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.58/1.59  tff(c_582, plain, (![B_116]: (r1_tarski(k2_pre_topc('#skF_2', B_116), '#skF_4') | ~r1_tarski(B_116, '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(B_116, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_477, c_568])).
% 3.58/1.59  tff(c_636, plain, (![B_121]: (r1_tarski(k2_pre_topc('#skF_2', B_121), '#skF_4') | ~r1_tarski(B_121, '#skF_4') | ~m1_subset_1(B_121, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_582])).
% 3.58/1.59  tff(c_640, plain, (![B_20]: (r1_tarski(k2_pre_topc('#skF_2', k1_tops_1('#skF_2', B_20)), '#skF_4') | ~r1_tarski(k1_tops_1('#skF_2', B_20), '#skF_4') | ~m1_subset_1(B_20, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_24, c_636])).
% 3.58/1.59  tff(c_646, plain, (![B_20]: (r1_tarski(k2_pre_topc('#skF_2', k1_tops_1('#skF_2', B_20)), '#skF_4') | ~r1_tarski(k1_tops_1('#skF_2', B_20), '#skF_4') | ~m1_subset_1(B_20, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_640])).
% 3.58/1.59  tff(c_535, plain, (![B_107, A_108]: (r1_tarski(B_107, k2_pre_topc(A_108, k1_tops_1(A_108, B_107))) | ~v4_tops_1(B_107, A_108) | ~m1_subset_1(B_107, k1_zfmisc_1(u1_struct_0(A_108))) | ~l1_pre_topc(A_108))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.58/1.59  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.58/1.59  tff(c_876, plain, (![A_138, B_139]: (k2_pre_topc(A_138, k1_tops_1(A_138, B_139))=B_139 | ~r1_tarski(k2_pre_topc(A_138, k1_tops_1(A_138, B_139)), B_139) | ~v4_tops_1(B_139, A_138) | ~m1_subset_1(B_139, k1_zfmisc_1(u1_struct_0(A_138))) | ~l1_pre_topc(A_138))), inference(resolution, [status(thm)], [c_535, c_2])).
% 3.58/1.59  tff(c_888, plain, (k2_pre_topc('#skF_2', k1_tops_1('#skF_2', '#skF_4'))='#skF_4' | ~v4_tops_1('#skF_4', '#skF_2') | ~l1_pre_topc('#skF_2') | ~r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_646, c_876])).
% 3.58/1.59  tff(c_904, plain, (k2_pre_topc('#skF_2', k1_tops_1('#skF_2', '#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_30, c_433, c_34, c_422, c_888])).
% 3.58/1.59  tff(c_20, plain, (![B_18, A_16]: (v5_tops_1(B_18, A_16) | k2_pre_topc(A_16, k1_tops_1(A_16, B_18))!=B_18 | ~m1_subset_1(B_18, k1_zfmisc_1(u1_struct_0(A_16))) | ~l1_pre_topc(A_16))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.58/1.59  tff(c_943, plain, (v5_tops_1('#skF_4', '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_904, c_20])).
% 3.58/1.59  tff(c_968, plain, (v5_tops_1('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_943])).
% 3.58/1.59  tff(c_970, plain, $false, inference(negUnitSimplification, [status(thm)], [c_53, c_968])).
% 3.58/1.59  tff(c_972, plain, (~v5_tops_1('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_50])).
% 3.58/1.59  tff(c_48, plain, (v4_tops_1('#skF_4', '#skF_2') | v5_tops_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.58/1.59  tff(c_973, plain, (v4_tops_1('#skF_4', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_972, c_48])).
% 3.58/1.59  tff(c_971, plain, (v4_pre_topc('#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_50])).
% 3.58/1.59  tff(c_1002, plain, (![A_144, B_145]: (k2_pre_topc(A_144, B_145)=B_145 | ~v4_pre_topc(B_145, A_144) | ~m1_subset_1(B_145, k1_zfmisc_1(u1_struct_0(A_144))) | ~l1_pre_topc(A_144))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.58/1.59  tff(c_1008, plain, (k2_pre_topc('#skF_2', '#skF_4')='#skF_4' | ~v4_pre_topc('#skF_4', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_30, c_1002])).
% 3.58/1.59  tff(c_1014, plain, (k2_pre_topc('#skF_2', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_971, c_1008])).
% 3.58/1.59  tff(c_1094, plain, (![A_166, B_167, C_168]: (r1_tarski(k2_pre_topc(A_166, B_167), k2_pre_topc(A_166, C_168)) | ~r1_tarski(B_167, C_168) | ~m1_subset_1(C_168, k1_zfmisc_1(u1_struct_0(A_166))) | ~m1_subset_1(B_167, k1_zfmisc_1(u1_struct_0(A_166))) | ~l1_pre_topc(A_166))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.58/1.59  tff(c_1102, plain, (![B_167]: (r1_tarski(k2_pre_topc('#skF_2', B_167), '#skF_4') | ~r1_tarski(B_167, '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(B_167, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1014, c_1094])).
% 3.58/1.59  tff(c_1122, plain, (![B_170]: (r1_tarski(k2_pre_topc('#skF_2', B_170), '#skF_4') | ~r1_tarski(B_170, '#skF_4') | ~m1_subset_1(B_170, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_1102])).
% 3.58/1.59  tff(c_1126, plain, (![B_20]: (r1_tarski(k2_pre_topc('#skF_2', k1_tops_1('#skF_2', B_20)), '#skF_4') | ~r1_tarski(k1_tops_1('#skF_2', B_20), '#skF_4') | ~m1_subset_1(B_20, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_24, c_1122])).
% 3.58/1.59  tff(c_1132, plain, (![B_20]: (r1_tarski(k2_pre_topc('#skF_2', k1_tops_1('#skF_2', B_20)), '#skF_4') | ~r1_tarski(k1_tops_1('#skF_2', B_20), '#skF_4') | ~m1_subset_1(B_20, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_1126])).
% 3.58/1.59  tff(c_1089, plain, (![B_162, A_163]: (r1_tarski(B_162, k2_pre_topc(A_163, k1_tops_1(A_163, B_162))) | ~v4_tops_1(B_162, A_163) | ~m1_subset_1(B_162, k1_zfmisc_1(u1_struct_0(A_163))) | ~l1_pre_topc(A_163))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.58/1.59  tff(c_1185, plain, (![A_179, B_180]: (k2_pre_topc(A_179, k1_tops_1(A_179, B_180))=B_180 | ~r1_tarski(k2_pre_topc(A_179, k1_tops_1(A_179, B_180)), B_180) | ~v4_tops_1(B_180, A_179) | ~m1_subset_1(B_180, k1_zfmisc_1(u1_struct_0(A_179))) | ~l1_pre_topc(A_179))), inference(resolution, [status(thm)], [c_1089, c_2])).
% 3.58/1.59  tff(c_1189, plain, (k2_pre_topc('#skF_2', k1_tops_1('#skF_2', '#skF_4'))='#skF_4' | ~v4_tops_1('#skF_4', '#skF_2') | ~l1_pre_topc('#skF_2') | ~r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_1132, c_1185])).
% 3.58/1.59  tff(c_1196, plain, (k2_pre_topc('#skF_2', k1_tops_1('#skF_2', '#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_30, c_993, c_34, c_973, c_1189])).
% 3.58/1.59  tff(c_1227, plain, (v5_tops_1('#skF_4', '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1196, c_20])).
% 3.58/1.59  tff(c_1250, plain, (v5_tops_1('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_1227])).
% 3.58/1.59  tff(c_1252, plain, $false, inference(negUnitSimplification, [status(thm)], [c_53, c_1250])).
% 3.58/1.59  tff(c_1253, plain, (v5_tops_1('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_46])).
% 3.58/1.59  tff(c_1343, plain, (![A_195, B_196]: (k2_pre_topc(A_195, k1_tops_1(A_195, B_196))=B_196 | ~v5_tops_1(B_196, A_195) | ~m1_subset_1(B_196, k1_zfmisc_1(u1_struct_0(A_195))) | ~l1_pre_topc(A_195))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.58/1.59  tff(c_1347, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_3'))='#skF_3' | ~v5_tops_1('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_1343])).
% 3.58/1.59  tff(c_1353, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_1253, c_1347])).
% 3.58/1.59  tff(c_1312, plain, (![A_189, B_190]: (m1_subset_1(k1_tops_1(A_189, B_190), k1_zfmisc_1(u1_struct_0(A_189))) | ~m1_subset_1(B_190, k1_zfmisc_1(u1_struct_0(A_189))) | ~l1_pre_topc(A_189))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.58/1.59  tff(c_1389, plain, (![A_199, B_200]: (v4_pre_topc(k2_pre_topc(A_199, k1_tops_1(A_199, B_200)), A_199) | ~v2_pre_topc(A_199) | ~m1_subset_1(B_200, k1_zfmisc_1(u1_struct_0(A_199))) | ~l1_pre_topc(A_199))), inference(resolution, [status(thm)], [c_1312, c_26])).
% 3.58/1.59  tff(c_1395, plain, (v4_pre_topc('#skF_3', '#skF_1') | ~v2_pre_topc('#skF_1') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1353, c_1389])).
% 3.58/1.59  tff(c_1400, plain, (v4_pre_topc('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_38, c_1395])).
% 3.58/1.59  tff(c_1402, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1264, c_1400])).
% 3.58/1.59  tff(c_1404, plain, (v4_pre_topc('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_44])).
% 3.58/1.59  tff(c_1254, plain, (v5_tops_1('#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_46])).
% 3.58/1.59  tff(c_40, plain, (~v5_tops_1('#skF_4', '#skF_2') | ~v4_tops_1('#skF_3', '#skF_1') | ~v4_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.58/1.59  tff(c_1406, plain, (~v4_tops_1('#skF_3', '#skF_1') | ~v4_pre_topc('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1254, c_40])).
% 3.58/1.59  tff(c_1407, plain, (~v4_pre_topc('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_1406])).
% 3.58/1.59  tff(c_1409, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1404, c_1407])).
% 3.58/1.59  tff(c_1410, plain, (~v4_tops_1('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_1406])).
% 3.58/1.59  tff(c_1415, plain, (![A_201, B_202]: (r1_tarski(k1_tops_1(A_201, B_202), B_202) | ~m1_subset_1(B_202, k1_zfmisc_1(u1_struct_0(A_201))) | ~l1_pre_topc(A_201))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.58/1.59  tff(c_1417, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_1415])).
% 3.58/1.59  tff(c_1422, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_1417])).
% 3.58/1.59  tff(c_1477, plain, (![A_211, B_212]: (k2_pre_topc(A_211, k1_tops_1(A_211, B_212))=B_212 | ~v5_tops_1(B_212, A_211) | ~m1_subset_1(B_212, k1_zfmisc_1(u1_struct_0(A_211))) | ~l1_pre_topc(A_211))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.58/1.59  tff(c_1481, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_3'))='#skF_3' | ~v5_tops_1('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_1477])).
% 3.58/1.59  tff(c_1487, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_1253, c_1481])).
% 3.58/1.59  tff(c_1434, plain, (![A_203, B_204]: (k2_pre_topc(A_203, B_204)=B_204 | ~v4_pre_topc(B_204, A_203) | ~m1_subset_1(B_204, k1_zfmisc_1(u1_struct_0(A_203))) | ~l1_pre_topc(A_203))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.58/1.59  tff(c_1437, plain, (k2_pre_topc('#skF_1', '#skF_3')='#skF_3' | ~v4_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_1434])).
% 3.58/1.59  tff(c_1443, plain, (k2_pre_topc('#skF_1', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_1404, c_1437])).
% 3.58/1.59  tff(c_1625, plain, (![B_229, A_230]: (v4_tops_1(B_229, A_230) | ~r1_tarski(B_229, k2_pre_topc(A_230, k1_tops_1(A_230, B_229))) | ~r1_tarski(k1_tops_1(A_230, k2_pre_topc(A_230, B_229)), B_229) | ~m1_subset_1(B_229, k1_zfmisc_1(u1_struct_0(A_230))) | ~l1_pre_topc(A_230))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.58/1.59  tff(c_1637, plain, (v4_tops_1('#skF_3', '#skF_1') | ~r1_tarski('#skF_3', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_3'))) | ~r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1443, c_1625])).
% 3.58/1.59  tff(c_1644, plain, (v4_tops_1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_1422, c_6, c_1487, c_1637])).
% 3.58/1.59  tff(c_1646, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1410, c_1644])).
% 3.58/1.59  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.58/1.59  
% 3.58/1.59  Inference rules
% 3.58/1.59  ----------------------
% 3.58/1.59  #Ref     : 0
% 3.58/1.59  #Sup     : 306
% 3.58/1.59  #Fact    : 0
% 3.58/1.59  #Define  : 0
% 3.58/1.59  #Split   : 41
% 3.58/1.59  #Chain   : 0
% 3.58/1.59  #Close   : 0
% 3.58/1.59  
% 3.58/1.59  Ordering : KBO
% 3.58/1.59  
% 3.58/1.59  Simplification rules
% 3.58/1.59  ----------------------
% 3.58/1.59  #Subsume      : 40
% 3.58/1.59  #Demod        : 457
% 3.58/1.59  #Tautology    : 103
% 3.58/1.59  #SimpNegUnit  : 19
% 3.58/1.59  #BackRed      : 2
% 3.58/1.59  
% 3.58/1.59  #Partial instantiations: 0
% 3.58/1.59  #Strategies tried      : 1
% 3.58/1.59  
% 3.58/1.59  Timing (in seconds)
% 3.58/1.59  ----------------------
% 3.58/1.59  Preprocessing        : 0.29
% 3.58/1.59  Parsing              : 0.16
% 3.58/1.59  CNF conversion       : 0.02
% 3.58/1.59  Main loop            : 0.52
% 3.58/1.59  Inferencing          : 0.19
% 3.58/1.60  Reduction            : 0.17
% 3.58/1.60  Demodulation         : 0.12
% 3.58/1.60  BG Simplification    : 0.02
% 3.58/1.60  Subsumption          : 0.10
% 3.58/1.60  Abstraction          : 0.02
% 3.58/1.60  MUC search           : 0.00
% 3.58/1.60  Cooper               : 0.00
% 3.58/1.60  Total                : 0.86
% 3.58/1.60  Index Insertion      : 0.00
% 3.58/1.60  Index Deletion       : 0.00
% 3.58/1.60  Index Matching       : 0.00
% 3.58/1.60  BG Taut test         : 0.00
%------------------------------------------------------------------------------
