%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:32 EST 2020

% Result     : Theorem 2.20s
% Output     : CNFRefutation 2.58s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 171 expanded)
%              Number of leaves         :   35 (  69 expanded)
%              Depth                    :    9
%              Number of atoms          :  150 ( 492 expanded)
%              Number of equality atoms :   10 (  10 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tsep_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k3_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(r1_tsep_1,type,(
    r1_tsep_1: ( $i * $i ) > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_127,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & m1_pre_topc(B,A) )
           => ! [C] :
                ( ( ~ v2_struct_0(C)
                  & m1_pre_topc(C,A) )
               => ( m1_pre_topc(B,C)
                 => ( ~ r1_tsep_1(B,C)
                    & ~ r1_tsep_1(C,B) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_tmap_1)).

tff(f_67,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_60,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_92,axiom,(
    ! [A,B] :
      ( ( l1_struct_0(A)
        & l1_struct_0(B) )
     => ( r1_tsep_1(A,B)
       => r1_tsep_1(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_99,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_52,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_84,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( l1_struct_0(B)
         => ( r1_tsep_1(A,B)
          <=> r1_xboole_0(u1_struct_0(A),u1_struct_0(B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tsep_1)).

tff(f_48,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_40,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_75,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_42,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_38,plain,(
    m1_pre_topc('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_291,plain,(
    ! [B_73,A_74] :
      ( l1_pre_topc(B_73)
      | ~ m1_pre_topc(B_73,A_74)
      | ~ l1_pre_topc(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_297,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_291])).

tff(c_304,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_297])).

tff(c_16,plain,(
    ! [A_12] :
      ( l1_struct_0(A_12)
      | ~ l1_pre_topc(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_34,plain,(
    m1_pre_topc('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_300,plain,
    ( l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_291])).

tff(c_307,plain,(
    l1_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_300])).

tff(c_40,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_58,plain,(
    ! [B_38,A_39] :
      ( l1_pre_topc(B_38)
      | ~ m1_pre_topc(B_38,A_39)
      | ~ l1_pre_topc(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_64,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_58])).

tff(c_71,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_64])).

tff(c_30,plain,
    ( r1_tsep_1('#skF_5','#skF_4')
    | r1_tsep_1('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_47,plain,(
    r1_tsep_1('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_88,plain,(
    ! [B_47,A_48] :
      ( r1_tsep_1(B_47,A_48)
      | ~ r1_tsep_1(A_48,B_47)
      | ~ l1_struct_0(B_47)
      | ~ l1_struct_0(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_91,plain,
    ( r1_tsep_1('#skF_5','#skF_4')
    | ~ l1_struct_0('#skF_5')
    | ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_47,c_88])).

tff(c_97,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_91])).

tff(c_100,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_16,c_97])).

tff(c_104,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_100])).

tff(c_106,plain,(
    l1_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_91])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_67,plain,
    ( l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_58])).

tff(c_74,plain,(
    l1_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_67])).

tff(c_32,plain,(
    m1_pre_topc('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_105,plain,
    ( ~ l1_struct_0('#skF_5')
    | r1_tsep_1('#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_91])).

tff(c_107,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_105])).

tff(c_110,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_16,c_107])).

tff(c_114,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_110])).

tff(c_116,plain,(
    l1_struct_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_105])).

tff(c_92,plain,(
    ! [B_49,A_50] :
      ( m1_subset_1(u1_struct_0(B_49),k1_zfmisc_1(u1_struct_0(A_50)))
      | ~ m1_pre_topc(B_49,A_50)
      | ~ l1_pre_topc(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_12,plain,(
    ! [A_10,B_11] :
      ( r1_tarski(A_10,B_11)
      | ~ m1_subset_1(A_10,k1_zfmisc_1(B_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_122,plain,(
    ! [B_51,A_52] :
      ( r1_tarski(u1_struct_0(B_51),u1_struct_0(A_52))
      | ~ m1_pre_topc(B_51,A_52)
      | ~ l1_pre_topc(A_52) ) ),
    inference(resolution,[status(thm)],[c_92,c_12])).

tff(c_10,plain,(
    ! [A_8,B_9] :
      ( k3_xboole_0(A_8,B_9) = A_8
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_126,plain,(
    ! [B_51,A_52] :
      ( k3_xboole_0(u1_struct_0(B_51),u1_struct_0(A_52)) = u1_struct_0(B_51)
      | ~ m1_pre_topc(B_51,A_52)
      | ~ l1_pre_topc(A_52) ) ),
    inference(resolution,[status(thm)],[c_122,c_10])).

tff(c_127,plain,(
    ! [A_53,B_54] :
      ( r1_xboole_0(u1_struct_0(A_53),u1_struct_0(B_54))
      | ~ r1_tsep_1(A_53,B_54)
      | ~ l1_struct_0(B_54)
      | ~ l1_struct_0(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_8,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | k1_xboole_0 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_76,plain,(
    ! [A_40,B_41,C_42] :
      ( ~ r1_xboole_0(A_40,B_41)
      | ~ r2_hidden(C_42,k3_xboole_0(A_40,B_41)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_81,plain,(
    ! [A_40,B_41] :
      ( ~ r1_xboole_0(A_40,B_41)
      | k3_xboole_0(A_40,B_41) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_76])).

tff(c_152,plain,(
    ! [A_59,B_60] :
      ( k3_xboole_0(u1_struct_0(A_59),u1_struct_0(B_60)) = k1_xboole_0
      | ~ r1_tsep_1(A_59,B_60)
      | ~ l1_struct_0(B_60)
      | ~ l1_struct_0(A_59) ) ),
    inference(resolution,[status(thm)],[c_127,c_81])).

tff(c_202,plain,(
    ! [B_69,A_70] :
      ( u1_struct_0(B_69) = k1_xboole_0
      | ~ r1_tsep_1(B_69,A_70)
      | ~ l1_struct_0(A_70)
      | ~ l1_struct_0(B_69)
      | ~ m1_pre_topc(B_69,A_70)
      | ~ l1_pre_topc(A_70) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_126,c_152])).

tff(c_208,plain,
    ( u1_struct_0('#skF_4') = k1_xboole_0
    | ~ l1_struct_0('#skF_5')
    | ~ l1_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_47,c_202])).

tff(c_214,plain,(
    u1_struct_0('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_32,c_106,c_116,c_208])).

tff(c_20,plain,(
    ! [A_16] :
      ( ~ v1_xboole_0(u1_struct_0(A_16))
      | ~ l1_struct_0(A_16)
      | v2_struct_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_258,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_214,c_20])).

tff(c_284,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_2,c_258])).

tff(c_286,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_284])).

tff(c_288,plain,(
    ~ r1_tsep_1('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_287,plain,(
    r1_tsep_1('#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_330,plain,(
    ! [B_89,A_90] :
      ( r1_tsep_1(B_89,A_90)
      | ~ r1_tsep_1(A_90,B_89)
      | ~ l1_struct_0(B_89)
      | ~ l1_struct_0(A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_332,plain,
    ( r1_tsep_1('#skF_4','#skF_5')
    | ~ l1_struct_0('#skF_4')
    | ~ l1_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_287,c_330])).

tff(c_335,plain,
    ( ~ l1_struct_0('#skF_4')
    | ~ l1_struct_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_288,c_332])).

tff(c_336,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_335])).

tff(c_339,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_16,c_336])).

tff(c_343,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_307,c_339])).

tff(c_344,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_335])).

tff(c_348,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_16,c_344])).

tff(c_352,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_304,c_348])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:10:08 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.20/1.28  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.20/1.29  
% 2.20/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.20/1.29  %$ r2_hidden > r1_xboole_0 > r1_tsep_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k3_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1
% 2.20/1.29  
% 2.20/1.29  %Foreground sorts:
% 2.20/1.29  
% 2.20/1.29  
% 2.20/1.29  %Background operators:
% 2.20/1.29  
% 2.20/1.29  
% 2.20/1.29  %Foreground operators:
% 2.20/1.29  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.20/1.29  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.20/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.20/1.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.20/1.29  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.20/1.29  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.20/1.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.20/1.29  tff('#skF_5', type, '#skF_5': $i).
% 2.20/1.29  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.20/1.29  tff('#skF_3', type, '#skF_3': $i).
% 2.20/1.29  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.20/1.29  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.20/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.20/1.29  tff('#skF_4', type, '#skF_4': $i).
% 2.20/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.20/1.29  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.20/1.29  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.20/1.29  tff(r1_tsep_1, type, r1_tsep_1: ($i * $i) > $o).
% 2.20/1.29  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.20/1.29  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.20/1.29  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.20/1.29  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.20/1.29  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.20/1.29  
% 2.20/1.31  tff(f_127, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (m1_pre_topc(B, C) => (~r1_tsep_1(B, C) & ~r1_tsep_1(C, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_tmap_1)).
% 2.20/1.31  tff(f_67, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 2.20/1.31  tff(f_60, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.20/1.31  tff(f_92, axiom, (![A, B]: ((l1_struct_0(A) & l1_struct_0(B)) => (r1_tsep_1(A, B) => r1_tsep_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_tsep_1)).
% 2.20/1.31  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.20/1.31  tff(f_99, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 2.58/1.31  tff(f_56, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.58/1.31  tff(f_52, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.58/1.31  tff(f_84, axiom, (![A]: (l1_struct_0(A) => (![B]: (l1_struct_0(B) => (r1_tsep_1(A, B) <=> r1_xboole_0(u1_struct_0(A), u1_struct_0(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tsep_1)).
% 2.58/1.31  tff(f_48, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.58/1.31  tff(f_40, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.58/1.31  tff(f_75, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.58/1.31  tff(c_42, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.58/1.31  tff(c_38, plain, (m1_pre_topc('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.58/1.31  tff(c_291, plain, (![B_73, A_74]: (l1_pre_topc(B_73) | ~m1_pre_topc(B_73, A_74) | ~l1_pre_topc(A_74))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.58/1.31  tff(c_297, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_38, c_291])).
% 2.58/1.31  tff(c_304, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_297])).
% 2.58/1.31  tff(c_16, plain, (![A_12]: (l1_struct_0(A_12) | ~l1_pre_topc(A_12))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.58/1.31  tff(c_34, plain, (m1_pre_topc('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.58/1.31  tff(c_300, plain, (l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_34, c_291])).
% 2.58/1.31  tff(c_307, plain, (l1_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_300])).
% 2.58/1.31  tff(c_40, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.58/1.31  tff(c_58, plain, (![B_38, A_39]: (l1_pre_topc(B_38) | ~m1_pre_topc(B_38, A_39) | ~l1_pre_topc(A_39))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.58/1.31  tff(c_64, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_38, c_58])).
% 2.58/1.31  tff(c_71, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_64])).
% 2.58/1.31  tff(c_30, plain, (r1_tsep_1('#skF_5', '#skF_4') | r1_tsep_1('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.58/1.31  tff(c_47, plain, (r1_tsep_1('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_30])).
% 2.58/1.31  tff(c_88, plain, (![B_47, A_48]: (r1_tsep_1(B_47, A_48) | ~r1_tsep_1(A_48, B_47) | ~l1_struct_0(B_47) | ~l1_struct_0(A_48))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.58/1.31  tff(c_91, plain, (r1_tsep_1('#skF_5', '#skF_4') | ~l1_struct_0('#skF_5') | ~l1_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_47, c_88])).
% 2.58/1.31  tff(c_97, plain, (~l1_struct_0('#skF_4')), inference(splitLeft, [status(thm)], [c_91])).
% 2.58/1.31  tff(c_100, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_16, c_97])).
% 2.58/1.31  tff(c_104, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_71, c_100])).
% 2.58/1.31  tff(c_106, plain, (l1_struct_0('#skF_4')), inference(splitRight, [status(thm)], [c_91])).
% 2.58/1.31  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.58/1.31  tff(c_67, plain, (l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_34, c_58])).
% 2.58/1.31  tff(c_74, plain, (l1_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_67])).
% 2.58/1.31  tff(c_32, plain, (m1_pre_topc('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.58/1.31  tff(c_105, plain, (~l1_struct_0('#skF_5') | r1_tsep_1('#skF_5', '#skF_4')), inference(splitRight, [status(thm)], [c_91])).
% 2.58/1.31  tff(c_107, plain, (~l1_struct_0('#skF_5')), inference(splitLeft, [status(thm)], [c_105])).
% 2.58/1.31  tff(c_110, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_16, c_107])).
% 2.58/1.31  tff(c_114, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_110])).
% 2.58/1.31  tff(c_116, plain, (l1_struct_0('#skF_5')), inference(splitRight, [status(thm)], [c_105])).
% 2.58/1.31  tff(c_92, plain, (![B_49, A_50]: (m1_subset_1(u1_struct_0(B_49), k1_zfmisc_1(u1_struct_0(A_50))) | ~m1_pre_topc(B_49, A_50) | ~l1_pre_topc(A_50))), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.58/1.31  tff(c_12, plain, (![A_10, B_11]: (r1_tarski(A_10, B_11) | ~m1_subset_1(A_10, k1_zfmisc_1(B_11)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.58/1.31  tff(c_122, plain, (![B_51, A_52]: (r1_tarski(u1_struct_0(B_51), u1_struct_0(A_52)) | ~m1_pre_topc(B_51, A_52) | ~l1_pre_topc(A_52))), inference(resolution, [status(thm)], [c_92, c_12])).
% 2.58/1.31  tff(c_10, plain, (![A_8, B_9]: (k3_xboole_0(A_8, B_9)=A_8 | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.58/1.31  tff(c_126, plain, (![B_51, A_52]: (k3_xboole_0(u1_struct_0(B_51), u1_struct_0(A_52))=u1_struct_0(B_51) | ~m1_pre_topc(B_51, A_52) | ~l1_pre_topc(A_52))), inference(resolution, [status(thm)], [c_122, c_10])).
% 2.58/1.31  tff(c_127, plain, (![A_53, B_54]: (r1_xboole_0(u1_struct_0(A_53), u1_struct_0(B_54)) | ~r1_tsep_1(A_53, B_54) | ~l1_struct_0(B_54) | ~l1_struct_0(A_53))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.58/1.31  tff(c_8, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | k1_xboole_0=A_6)), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.58/1.31  tff(c_76, plain, (![A_40, B_41, C_42]: (~r1_xboole_0(A_40, B_41) | ~r2_hidden(C_42, k3_xboole_0(A_40, B_41)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.58/1.31  tff(c_81, plain, (![A_40, B_41]: (~r1_xboole_0(A_40, B_41) | k3_xboole_0(A_40, B_41)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_76])).
% 2.58/1.31  tff(c_152, plain, (![A_59, B_60]: (k3_xboole_0(u1_struct_0(A_59), u1_struct_0(B_60))=k1_xboole_0 | ~r1_tsep_1(A_59, B_60) | ~l1_struct_0(B_60) | ~l1_struct_0(A_59))), inference(resolution, [status(thm)], [c_127, c_81])).
% 2.58/1.31  tff(c_202, plain, (![B_69, A_70]: (u1_struct_0(B_69)=k1_xboole_0 | ~r1_tsep_1(B_69, A_70) | ~l1_struct_0(A_70) | ~l1_struct_0(B_69) | ~m1_pre_topc(B_69, A_70) | ~l1_pre_topc(A_70))), inference(superposition, [status(thm), theory('equality')], [c_126, c_152])).
% 2.58/1.31  tff(c_208, plain, (u1_struct_0('#skF_4')=k1_xboole_0 | ~l1_struct_0('#skF_5') | ~l1_struct_0('#skF_4') | ~m1_pre_topc('#skF_4', '#skF_5') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_47, c_202])).
% 2.58/1.31  tff(c_214, plain, (u1_struct_0('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_74, c_32, c_106, c_116, c_208])).
% 2.58/1.31  tff(c_20, plain, (![A_16]: (~v1_xboole_0(u1_struct_0(A_16)) | ~l1_struct_0(A_16) | v2_struct_0(A_16))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.58/1.31  tff(c_258, plain, (~v1_xboole_0(k1_xboole_0) | ~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_214, c_20])).
% 2.58/1.31  tff(c_284, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_106, c_2, c_258])).
% 2.58/1.31  tff(c_286, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_284])).
% 2.58/1.31  tff(c_288, plain, (~r1_tsep_1('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_30])).
% 2.58/1.31  tff(c_287, plain, (r1_tsep_1('#skF_5', '#skF_4')), inference(splitRight, [status(thm)], [c_30])).
% 2.58/1.31  tff(c_330, plain, (![B_89, A_90]: (r1_tsep_1(B_89, A_90) | ~r1_tsep_1(A_90, B_89) | ~l1_struct_0(B_89) | ~l1_struct_0(A_90))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.58/1.31  tff(c_332, plain, (r1_tsep_1('#skF_4', '#skF_5') | ~l1_struct_0('#skF_4') | ~l1_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_287, c_330])).
% 2.58/1.31  tff(c_335, plain, (~l1_struct_0('#skF_4') | ~l1_struct_0('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_288, c_332])).
% 2.58/1.31  tff(c_336, plain, (~l1_struct_0('#skF_5')), inference(splitLeft, [status(thm)], [c_335])).
% 2.58/1.31  tff(c_339, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_16, c_336])).
% 2.58/1.31  tff(c_343, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_307, c_339])).
% 2.58/1.31  tff(c_344, plain, (~l1_struct_0('#skF_4')), inference(splitRight, [status(thm)], [c_335])).
% 2.58/1.31  tff(c_348, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_16, c_344])).
% 2.58/1.31  tff(c_352, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_304, c_348])).
% 2.58/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.58/1.31  
% 2.58/1.31  Inference rules
% 2.58/1.31  ----------------------
% 2.58/1.31  #Ref     : 0
% 2.58/1.31  #Sup     : 57
% 2.58/1.31  #Fact    : 0
% 2.58/1.31  #Define  : 0
% 2.58/1.31  #Split   : 5
% 2.58/1.31  #Chain   : 0
% 2.58/1.31  #Close   : 0
% 2.58/1.31  
% 2.58/1.31  Ordering : KBO
% 2.58/1.31  
% 2.58/1.31  Simplification rules
% 2.58/1.31  ----------------------
% 2.58/1.31  #Subsume      : 6
% 2.58/1.31  #Demod        : 37
% 2.58/1.31  #Tautology    : 14
% 2.58/1.31  #SimpNegUnit  : 2
% 2.58/1.31  #BackRed      : 0
% 2.58/1.31  
% 2.58/1.31  #Partial instantiations: 0
% 2.58/1.31  #Strategies tried      : 1
% 2.58/1.31  
% 2.58/1.31  Timing (in seconds)
% 2.58/1.31  ----------------------
% 2.58/1.32  Preprocessing        : 0.30
% 2.58/1.32  Parsing              : 0.17
% 2.58/1.32  CNF conversion       : 0.02
% 2.58/1.32  Main loop            : 0.24
% 2.58/1.32  Inferencing          : 0.10
% 2.58/1.32  Reduction            : 0.07
% 2.58/1.32  Demodulation         : 0.05
% 2.58/1.32  BG Simplification    : 0.01
% 2.58/1.32  Subsumption          : 0.04
% 2.58/1.32  Abstraction          : 0.01
% 2.58/1.32  MUC search           : 0.00
% 2.58/1.32  Cooper               : 0.00
% 2.58/1.32  Total                : 0.59
% 2.58/1.32  Index Insertion      : 0.00
% 2.58/1.32  Index Deletion       : 0.00
% 2.58/1.32  Index Matching       : 0.00
% 2.58/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
