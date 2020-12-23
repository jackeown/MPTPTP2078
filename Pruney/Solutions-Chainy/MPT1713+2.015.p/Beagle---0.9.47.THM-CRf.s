%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:31 EST 2020

% Result     : Theorem 2.32s
% Output     : CNFRefutation 2.32s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 168 expanded)
%              Number of leaves         :   33 (  67 expanded)
%              Depth                    :   10
%              Number of atoms          :  147 ( 489 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tsep_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k3_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_124,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_tmap_1)).

tff(f_64,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_57,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_89,axiom,(
    ! [A,B] :
      ( ( l1_struct_0(A)
        & l1_struct_0(B) )
     => ( r1_tsep_1(A,B)
       => r1_tsep_1(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).

tff(f_81,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( l1_struct_0(B)
         => ( r1_tsep_1(A,B)
          <=> r1_xboole_0(u1_struct_0(A),u1_struct_0(B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tsep_1)).

tff(f_96,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_72,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_42,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_38,plain,(
    m1_pre_topc('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_224,plain,(
    ! [B_81,A_82] :
      ( l1_pre_topc(B_81)
      | ~ m1_pre_topc(B_81,A_82)
      | ~ l1_pre_topc(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_227,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_224])).

tff(c_236,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_227])).

tff(c_16,plain,(
    ! [A_14] :
      ( l1_struct_0(A_14)
      | ~ l1_pre_topc(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_34,plain,(
    m1_pre_topc('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_230,plain,
    ( l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_224])).

tff(c_239,plain,(
    l1_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_230])).

tff(c_40,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_55,plain,(
    ! [B_35,A_36] :
      ( l1_pre_topc(B_35)
      | ~ m1_pre_topc(B_35,A_36)
      | ~ l1_pre_topc(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_58,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_55])).

tff(c_67,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_58])).

tff(c_30,plain,
    ( r1_tsep_1('#skF_5','#skF_4')
    | r1_tsep_1('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_48,plain,(
    r1_tsep_1('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_103,plain,(
    ! [B_53,A_54] :
      ( r1_tsep_1(B_53,A_54)
      | ~ r1_tsep_1(A_54,B_53)
      | ~ l1_struct_0(B_53)
      | ~ l1_struct_0(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_106,plain,
    ( r1_tsep_1('#skF_5','#skF_4')
    | ~ l1_struct_0('#skF_5')
    | ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_103])).

tff(c_107,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_106])).

tff(c_110,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_16,c_107])).

tff(c_114,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_110])).

tff(c_116,plain,(
    l1_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_106])).

tff(c_61,plain,
    ( l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_55])).

tff(c_70,plain,(
    l1_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_61])).

tff(c_115,plain,
    ( ~ l1_struct_0('#skF_5')
    | r1_tsep_1('#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_106])).

tff(c_117,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_115])).

tff(c_120,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_16,c_117])).

tff(c_124,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_120])).

tff(c_126,plain,(
    l1_struct_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_115])).

tff(c_32,plain,(
    m1_pre_topc('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_24,plain,(
    ! [A_19,B_21] :
      ( r1_xboole_0(u1_struct_0(A_19),u1_struct_0(B_21))
      | ~ r1_tsep_1(A_19,B_21)
      | ~ l1_struct_0(B_21)
      | ~ l1_struct_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_132,plain,(
    ! [B_55,A_56] :
      ( m1_subset_1(u1_struct_0(B_55),k1_zfmisc_1(u1_struct_0(A_56)))
      | ~ m1_pre_topc(B_55,A_56)
      | ~ l1_pre_topc(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_12,plain,(
    ! [A_12,B_13] :
      ( r1_tarski(A_12,B_13)
      | ~ m1_subset_1(A_12,k1_zfmisc_1(B_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_137,plain,(
    ! [B_57,A_58] :
      ( r1_tarski(u1_struct_0(B_57),u1_struct_0(A_58))
      | ~ m1_pre_topc(B_57,A_58)
      | ~ l1_pre_topc(A_58) ) ),
    inference(resolution,[status(thm)],[c_132,c_12])).

tff(c_10,plain,(
    ! [A_10,B_11] :
      ( k3_xboole_0(A_10,B_11) = A_10
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_148,plain,(
    ! [B_63,A_64] :
      ( k3_xboole_0(u1_struct_0(B_63),u1_struct_0(A_64)) = u1_struct_0(B_63)
      | ~ m1_pre_topc(B_63,A_64)
      | ~ l1_pre_topc(A_64) ) ),
    inference(resolution,[status(thm)],[c_137,c_10])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_82,plain,(
    ! [A_44,B_45,C_46] :
      ( ~ r1_xboole_0(A_44,B_45)
      | ~ r2_hidden(C_46,k3_xboole_0(A_44,B_45)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_87,plain,(
    ! [A_44,B_45] :
      ( ~ r1_xboole_0(A_44,B_45)
      | v1_xboole_0(k3_xboole_0(A_44,B_45)) ) ),
    inference(resolution,[status(thm)],[c_4,c_82])).

tff(c_181,plain,(
    ! [B_70,A_71] :
      ( ~ r1_xboole_0(u1_struct_0(B_70),u1_struct_0(A_71))
      | v1_xboole_0(u1_struct_0(B_70))
      | ~ m1_pre_topc(B_70,A_71)
      | ~ l1_pre_topc(A_71) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_148,c_87])).

tff(c_191,plain,(
    ! [A_74,B_75] :
      ( v1_xboole_0(u1_struct_0(A_74))
      | ~ m1_pre_topc(A_74,B_75)
      | ~ l1_pre_topc(B_75)
      | ~ r1_tsep_1(A_74,B_75)
      | ~ l1_struct_0(B_75)
      | ~ l1_struct_0(A_74) ) ),
    inference(resolution,[status(thm)],[c_24,c_181])).

tff(c_195,plain,
    ( v1_xboole_0(u1_struct_0('#skF_4'))
    | ~ m1_pre_topc('#skF_4','#skF_5')
    | ~ l1_pre_topc('#skF_5')
    | ~ l1_struct_0('#skF_5')
    | ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_191])).

tff(c_201,plain,(
    v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_126,c_70,c_32,c_195])).

tff(c_20,plain,(
    ! [A_18] :
      ( ~ v1_xboole_0(u1_struct_0(A_18))
      | ~ l1_struct_0(A_18)
      | v2_struct_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_206,plain,
    ( ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_201,c_20])).

tff(c_212,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_206])).

tff(c_214,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_212])).

tff(c_216,plain,(
    ~ r1_tsep_1('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_215,plain,(
    r1_tsep_1('#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_266,plain,(
    ! [B_95,A_96] :
      ( r1_tsep_1(B_95,A_96)
      | ~ r1_tsep_1(A_96,B_95)
      | ~ l1_struct_0(B_95)
      | ~ l1_struct_0(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_268,plain,
    ( r1_tsep_1('#skF_4','#skF_5')
    | ~ l1_struct_0('#skF_4')
    | ~ l1_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_215,c_266])).

tff(c_271,plain,
    ( ~ l1_struct_0('#skF_4')
    | ~ l1_struct_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_216,c_268])).

tff(c_272,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_271])).

tff(c_275,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_16,c_272])).

tff(c_279,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_239,c_275])).

tff(c_280,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_271])).

tff(c_284,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_16,c_280])).

tff(c_288,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_236,c_284])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n011.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:23:57 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.32/1.33  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.32/1.34  
% 2.32/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.32/1.35  %$ r2_hidden > r1_xboole_0 > r1_tsep_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k3_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2
% 2.32/1.35  
% 2.32/1.35  %Foreground sorts:
% 2.32/1.35  
% 2.32/1.35  
% 2.32/1.35  %Background operators:
% 2.32/1.35  
% 2.32/1.35  
% 2.32/1.35  %Foreground operators:
% 2.32/1.35  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.32/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.32/1.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.32/1.35  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.32/1.35  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.32/1.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.32/1.35  tff('#skF_5', type, '#skF_5': $i).
% 2.32/1.35  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.32/1.35  tff('#skF_3', type, '#skF_3': $i).
% 2.32/1.35  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.32/1.35  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.32/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.32/1.35  tff('#skF_4', type, '#skF_4': $i).
% 2.32/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.32/1.35  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.32/1.35  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.32/1.35  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.32/1.35  tff(r1_tsep_1, type, r1_tsep_1: ($i * $i) > $o).
% 2.32/1.35  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.32/1.35  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.32/1.35  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.32/1.35  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.32/1.35  
% 2.32/1.36  tff(f_124, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (m1_pre_topc(B, C) => (~r1_tsep_1(B, C) & ~r1_tsep_1(C, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_tmap_1)).
% 2.32/1.36  tff(f_64, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 2.32/1.36  tff(f_57, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.32/1.36  tff(f_89, axiom, (![A, B]: ((l1_struct_0(A) & l1_struct_0(B)) => (r1_tsep_1(A, B) => r1_tsep_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_tsep_1)).
% 2.32/1.36  tff(f_81, axiom, (![A]: (l1_struct_0(A) => (![B]: (l1_struct_0(B) => (r1_tsep_1(A, B) <=> r1_xboole_0(u1_struct_0(A), u1_struct_0(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tsep_1)).
% 2.32/1.36  tff(f_96, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 2.32/1.36  tff(f_53, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.32/1.36  tff(f_49, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.32/1.36  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.32/1.36  tff(f_45, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.32/1.36  tff(f_72, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.32/1.36  tff(c_42, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_124])).
% 2.32/1.36  tff(c_38, plain, (m1_pre_topc('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_124])).
% 2.32/1.36  tff(c_224, plain, (![B_81, A_82]: (l1_pre_topc(B_81) | ~m1_pre_topc(B_81, A_82) | ~l1_pre_topc(A_82))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.32/1.36  tff(c_227, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_38, c_224])).
% 2.32/1.36  tff(c_236, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_227])).
% 2.32/1.36  tff(c_16, plain, (![A_14]: (l1_struct_0(A_14) | ~l1_pre_topc(A_14))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.32/1.36  tff(c_34, plain, (m1_pre_topc('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_124])).
% 2.32/1.36  tff(c_230, plain, (l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_34, c_224])).
% 2.32/1.36  tff(c_239, plain, (l1_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_230])).
% 2.32/1.36  tff(c_40, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_124])).
% 2.32/1.36  tff(c_55, plain, (![B_35, A_36]: (l1_pre_topc(B_35) | ~m1_pre_topc(B_35, A_36) | ~l1_pre_topc(A_36))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.32/1.36  tff(c_58, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_38, c_55])).
% 2.32/1.36  tff(c_67, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_58])).
% 2.32/1.36  tff(c_30, plain, (r1_tsep_1('#skF_5', '#skF_4') | r1_tsep_1('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_124])).
% 2.32/1.36  tff(c_48, plain, (r1_tsep_1('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_30])).
% 2.32/1.36  tff(c_103, plain, (![B_53, A_54]: (r1_tsep_1(B_53, A_54) | ~r1_tsep_1(A_54, B_53) | ~l1_struct_0(B_53) | ~l1_struct_0(A_54))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.32/1.36  tff(c_106, plain, (r1_tsep_1('#skF_5', '#skF_4') | ~l1_struct_0('#skF_5') | ~l1_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_48, c_103])).
% 2.32/1.36  tff(c_107, plain, (~l1_struct_0('#skF_4')), inference(splitLeft, [status(thm)], [c_106])).
% 2.32/1.36  tff(c_110, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_16, c_107])).
% 2.32/1.36  tff(c_114, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_67, c_110])).
% 2.32/1.36  tff(c_116, plain, (l1_struct_0('#skF_4')), inference(splitRight, [status(thm)], [c_106])).
% 2.32/1.36  tff(c_61, plain, (l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_34, c_55])).
% 2.32/1.36  tff(c_70, plain, (l1_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_61])).
% 2.32/1.36  tff(c_115, plain, (~l1_struct_0('#skF_5') | r1_tsep_1('#skF_5', '#skF_4')), inference(splitRight, [status(thm)], [c_106])).
% 2.32/1.36  tff(c_117, plain, (~l1_struct_0('#skF_5')), inference(splitLeft, [status(thm)], [c_115])).
% 2.32/1.36  tff(c_120, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_16, c_117])).
% 2.32/1.36  tff(c_124, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_120])).
% 2.32/1.36  tff(c_126, plain, (l1_struct_0('#skF_5')), inference(splitRight, [status(thm)], [c_115])).
% 2.32/1.36  tff(c_32, plain, (m1_pre_topc('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_124])).
% 2.32/1.36  tff(c_24, plain, (![A_19, B_21]: (r1_xboole_0(u1_struct_0(A_19), u1_struct_0(B_21)) | ~r1_tsep_1(A_19, B_21) | ~l1_struct_0(B_21) | ~l1_struct_0(A_19))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.32/1.36  tff(c_132, plain, (![B_55, A_56]: (m1_subset_1(u1_struct_0(B_55), k1_zfmisc_1(u1_struct_0(A_56))) | ~m1_pre_topc(B_55, A_56) | ~l1_pre_topc(A_56))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.32/1.36  tff(c_12, plain, (![A_12, B_13]: (r1_tarski(A_12, B_13) | ~m1_subset_1(A_12, k1_zfmisc_1(B_13)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.32/1.36  tff(c_137, plain, (![B_57, A_58]: (r1_tarski(u1_struct_0(B_57), u1_struct_0(A_58)) | ~m1_pre_topc(B_57, A_58) | ~l1_pre_topc(A_58))), inference(resolution, [status(thm)], [c_132, c_12])).
% 2.32/1.36  tff(c_10, plain, (![A_10, B_11]: (k3_xboole_0(A_10, B_11)=A_10 | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.32/1.36  tff(c_148, plain, (![B_63, A_64]: (k3_xboole_0(u1_struct_0(B_63), u1_struct_0(A_64))=u1_struct_0(B_63) | ~m1_pre_topc(B_63, A_64) | ~l1_pre_topc(A_64))), inference(resolution, [status(thm)], [c_137, c_10])).
% 2.32/1.36  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.32/1.36  tff(c_82, plain, (![A_44, B_45, C_46]: (~r1_xboole_0(A_44, B_45) | ~r2_hidden(C_46, k3_xboole_0(A_44, B_45)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.32/1.36  tff(c_87, plain, (![A_44, B_45]: (~r1_xboole_0(A_44, B_45) | v1_xboole_0(k3_xboole_0(A_44, B_45)))), inference(resolution, [status(thm)], [c_4, c_82])).
% 2.32/1.36  tff(c_181, plain, (![B_70, A_71]: (~r1_xboole_0(u1_struct_0(B_70), u1_struct_0(A_71)) | v1_xboole_0(u1_struct_0(B_70)) | ~m1_pre_topc(B_70, A_71) | ~l1_pre_topc(A_71))), inference(superposition, [status(thm), theory('equality')], [c_148, c_87])).
% 2.32/1.36  tff(c_191, plain, (![A_74, B_75]: (v1_xboole_0(u1_struct_0(A_74)) | ~m1_pre_topc(A_74, B_75) | ~l1_pre_topc(B_75) | ~r1_tsep_1(A_74, B_75) | ~l1_struct_0(B_75) | ~l1_struct_0(A_74))), inference(resolution, [status(thm)], [c_24, c_181])).
% 2.32/1.36  tff(c_195, plain, (v1_xboole_0(u1_struct_0('#skF_4')) | ~m1_pre_topc('#skF_4', '#skF_5') | ~l1_pre_topc('#skF_5') | ~l1_struct_0('#skF_5') | ~l1_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_48, c_191])).
% 2.32/1.36  tff(c_201, plain, (v1_xboole_0(u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_116, c_126, c_70, c_32, c_195])).
% 2.32/1.36  tff(c_20, plain, (![A_18]: (~v1_xboole_0(u1_struct_0(A_18)) | ~l1_struct_0(A_18) | v2_struct_0(A_18))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.32/1.36  tff(c_206, plain, (~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_201, c_20])).
% 2.32/1.36  tff(c_212, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_116, c_206])).
% 2.32/1.36  tff(c_214, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_212])).
% 2.32/1.36  tff(c_216, plain, (~r1_tsep_1('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_30])).
% 2.32/1.36  tff(c_215, plain, (r1_tsep_1('#skF_5', '#skF_4')), inference(splitRight, [status(thm)], [c_30])).
% 2.32/1.36  tff(c_266, plain, (![B_95, A_96]: (r1_tsep_1(B_95, A_96) | ~r1_tsep_1(A_96, B_95) | ~l1_struct_0(B_95) | ~l1_struct_0(A_96))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.32/1.36  tff(c_268, plain, (r1_tsep_1('#skF_4', '#skF_5') | ~l1_struct_0('#skF_4') | ~l1_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_215, c_266])).
% 2.32/1.36  tff(c_271, plain, (~l1_struct_0('#skF_4') | ~l1_struct_0('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_216, c_268])).
% 2.32/1.36  tff(c_272, plain, (~l1_struct_0('#skF_5')), inference(splitLeft, [status(thm)], [c_271])).
% 2.32/1.36  tff(c_275, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_16, c_272])).
% 2.32/1.36  tff(c_279, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_239, c_275])).
% 2.32/1.36  tff(c_280, plain, (~l1_struct_0('#skF_4')), inference(splitRight, [status(thm)], [c_271])).
% 2.32/1.36  tff(c_284, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_16, c_280])).
% 2.32/1.36  tff(c_288, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_236, c_284])).
% 2.32/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.32/1.36  
% 2.32/1.36  Inference rules
% 2.32/1.36  ----------------------
% 2.32/1.36  #Ref     : 0
% 2.32/1.36  #Sup     : 42
% 2.32/1.36  #Fact    : 0
% 2.32/1.36  #Define  : 0
% 2.32/1.36  #Split   : 4
% 2.32/1.36  #Chain   : 0
% 2.32/1.36  #Close   : 0
% 2.32/1.36  
% 2.32/1.36  Ordering : KBO
% 2.32/1.36  
% 2.32/1.36  Simplification rules
% 2.32/1.36  ----------------------
% 2.32/1.36  #Subsume      : 1
% 2.32/1.36  #Demod        : 24
% 2.32/1.36  #Tautology    : 14
% 2.32/1.36  #SimpNegUnit  : 2
% 2.32/1.36  #BackRed      : 0
% 2.32/1.36  
% 2.32/1.36  #Partial instantiations: 0
% 2.32/1.36  #Strategies tried      : 1
% 2.32/1.36  
% 2.32/1.36  Timing (in seconds)
% 2.32/1.36  ----------------------
% 2.32/1.37  Preprocessing        : 0.32
% 2.32/1.37  Parsing              : 0.18
% 2.32/1.37  CNF conversion       : 0.02
% 2.32/1.37  Main loop            : 0.22
% 2.32/1.37  Inferencing          : 0.09
% 2.32/1.37  Reduction            : 0.05
% 2.32/1.37  Demodulation         : 0.04
% 2.32/1.37  BG Simplification    : 0.01
% 2.32/1.37  Subsumption          : 0.03
% 2.32/1.37  Abstraction          : 0.01
% 2.32/1.37  MUC search           : 0.00
% 2.32/1.37  Cooper               : 0.00
% 2.32/1.37  Total                : 0.58
% 2.32/1.37  Index Insertion      : 0.00
% 2.32/1.37  Index Deletion       : 0.00
% 2.32/1.37  Index Matching       : 0.00
% 2.32/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
