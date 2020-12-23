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
% DateTime   : Thu Dec  3 10:22:56 EST 2020

% Result     : Theorem 16.56s
% Output     : CNFRefutation 16.80s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 174 expanded)
%              Number of leaves         :   32 (  76 expanded)
%              Depth                    :   11
%              Number of atoms          :  179 ( 448 expanded)
%              Number of equality atoms :    1 (   4 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v1_tops_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k5_setfam_1 > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_5 > #skF_4 > #skF_3 > #skF_9 > #skF_8 > #skF_2 > #skF_7 > #skF_1 > #skF_6

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#skF_4',type,(
    '#skF_4': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_tops_2,type,(
    v1_tops_2: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k5_setfam_1,type,(
    k5_setfam_1: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_107,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
           => ( v1_tops_2(B,A)
             => v3_pre_topc(k5_setfam_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_tops_2)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_39,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_81,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_pre_topc(B,A)
          <=> r2_hidden(B,u1_pre_topc(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_pre_topc)).

tff(f_95,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
         => ( v1_tops_2(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( r2_hidden(C,B)
                 => v3_pre_topc(C,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_2)).

tff(f_72,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v2_pre_topc(A)
      <=> ( r2_hidden(u1_struct_0(A),u1_pre_topc(A))
          & ! [B] :
              ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
             => ( r1_tarski(B,u1_pre_topc(A))
               => r2_hidden(k5_setfam_1(u1_struct_0(A),B),u1_pre_topc(A)) ) )
          & ! [B] :
              ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
             => ! [C] :
                  ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
                 => ( ( r2_hidden(B,u1_pre_topc(A))
                      & r2_hidden(C,u1_pre_topc(A)) )
                   => r2_hidden(k9_subset_1(u1_struct_0(A),B,C),u1_pre_topc(A)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_pre_topc)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k5_setfam_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_setfam_1)).

tff(c_74,plain,(
    ~ v3_pre_topc(k5_setfam_1(u1_struct_0('#skF_8'),'#skF_9'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_105,plain,(
    ! [A_53,B_54] :
      ( ~ r2_hidden('#skF_1'(A_53,B_54),B_54)
      | r1_tarski(A_53,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_114,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_105])).

tff(c_78,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_8')))) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_80,plain,(
    l1_pre_topc('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_82,plain,(
    v2_pre_topc('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_84,plain,(
    ! [A_45,B_46] :
      ( r1_tarski(A_45,B_46)
      | ~ m1_subset_1(A_45,k1_zfmisc_1(B_46)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_88,plain,(
    r1_tarski('#skF_9',k1_zfmisc_1(u1_struct_0('#skF_8'))) ),
    inference(resolution,[status(thm)],[c_78,c_84])).

tff(c_117,plain,(
    ! [C_56,B_57,A_58] :
      ( r2_hidden(C_56,B_57)
      | ~ r2_hidden(C_56,A_58)
      | ~ r1_tarski(A_58,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_159,plain,(
    ! [A_73,B_74,B_75] :
      ( r2_hidden('#skF_1'(A_73,B_74),B_75)
      | ~ r1_tarski(A_73,B_75)
      | r1_tarski(A_73,B_74) ) ),
    inference(resolution,[status(thm)],[c_6,c_117])).

tff(c_8,plain,(
    ! [C_10,A_6] :
      ( r1_tarski(C_10,A_6)
      | ~ r2_hidden(C_10,k1_zfmisc_1(A_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_172,plain,(
    ! [A_73,B_74,A_6] :
      ( r1_tarski('#skF_1'(A_73,B_74),A_6)
      | ~ r1_tarski(A_73,k1_zfmisc_1(A_6))
      | r1_tarski(A_73,B_74) ) ),
    inference(resolution,[status(thm)],[c_159,c_8])).

tff(c_122,plain,(
    ! [A_1,B_2,B_57] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_57)
      | ~ r1_tarski(A_1,B_57)
      | r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_117])).

tff(c_24,plain,(
    ! [A_13,B_14] :
      ( m1_subset_1(A_13,k1_zfmisc_1(B_14))
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_212,plain,(
    ! [B_89,A_90] :
      ( v3_pre_topc(B_89,A_90)
      | ~ r2_hidden(B_89,u1_pre_topc(A_90))
      | ~ m1_subset_1(B_89,k1_zfmisc_1(u1_struct_0(A_90)))
      | ~ l1_pre_topc(A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_223,plain,(
    ! [A_91,A_92] :
      ( v3_pre_topc(A_91,A_92)
      | ~ r2_hidden(A_91,u1_pre_topc(A_92))
      | ~ l1_pre_topc(A_92)
      | ~ r1_tarski(A_91,u1_struct_0(A_92)) ) ),
    inference(resolution,[status(thm)],[c_24,c_212])).

tff(c_4853,plain,(
    ! [A_409,B_410,A_411] :
      ( v3_pre_topc('#skF_1'(A_409,B_410),A_411)
      | ~ l1_pre_topc(A_411)
      | ~ r1_tarski('#skF_1'(A_409,B_410),u1_struct_0(A_411))
      | ~ r1_tarski(A_409,u1_pre_topc(A_411))
      | r1_tarski(A_409,B_410) ) ),
    inference(resolution,[status(thm)],[c_122,c_223])).

tff(c_4910,plain,(
    ! [A_414,B_415,A_416] :
      ( v3_pre_topc('#skF_1'(A_414,B_415),A_416)
      | ~ l1_pre_topc(A_416)
      | ~ r1_tarski(A_414,u1_pre_topc(A_416))
      | ~ r1_tarski(A_414,k1_zfmisc_1(u1_struct_0(A_416)))
      | r1_tarski(A_414,B_415) ) ),
    inference(resolution,[status(thm)],[c_172,c_4853])).

tff(c_5000,plain,(
    ! [B_415] :
      ( v3_pre_topc('#skF_1'('#skF_9',B_415),'#skF_8')
      | ~ l1_pre_topc('#skF_8')
      | ~ r1_tarski('#skF_9',u1_pre_topc('#skF_8'))
      | r1_tarski('#skF_9',B_415) ) ),
    inference(resolution,[status(thm)],[c_88,c_4910])).

tff(c_5052,plain,(
    ! [B_415] :
      ( v3_pre_topc('#skF_1'('#skF_9',B_415),'#skF_8')
      | ~ r1_tarski('#skF_9',u1_pre_topc('#skF_8'))
      | r1_tarski('#skF_9',B_415) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_5000])).

tff(c_5053,plain,(
    ~ r1_tarski('#skF_9',u1_pre_topc('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_5052])).

tff(c_76,plain,(
    v1_tops_2('#skF_9','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_2452,plain,(
    ! [C_255,A_256,B_257] :
      ( v3_pre_topc(C_255,A_256)
      | ~ r2_hidden(C_255,B_257)
      | ~ m1_subset_1(C_255,k1_zfmisc_1(u1_struct_0(A_256)))
      | ~ v1_tops_2(B_257,A_256)
      | ~ m1_subset_1(B_257,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_256))))
      | ~ l1_pre_topc(A_256) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_8659,plain,(
    ! [A_578,B_579,A_580] :
      ( v3_pre_topc('#skF_1'(A_578,B_579),A_580)
      | ~ m1_subset_1('#skF_1'(A_578,B_579),k1_zfmisc_1(u1_struct_0(A_580)))
      | ~ v1_tops_2(A_578,A_580)
      | ~ m1_subset_1(A_578,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_580))))
      | ~ l1_pre_topc(A_580)
      | r1_tarski(A_578,B_579) ) ),
    inference(resolution,[status(thm)],[c_6,c_2452])).

tff(c_22536,plain,(
    ! [A_915,B_916,A_917] :
      ( v3_pre_topc('#skF_1'(A_915,B_916),A_917)
      | ~ v1_tops_2(A_915,A_917)
      | ~ m1_subset_1(A_915,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_917))))
      | ~ l1_pre_topc(A_917)
      | r1_tarski(A_915,B_916)
      | ~ r1_tarski('#skF_1'(A_915,B_916),u1_struct_0(A_917)) ) ),
    inference(resolution,[status(thm)],[c_24,c_8659])).

tff(c_22552,plain,(
    ! [B_916] :
      ( v3_pre_topc('#skF_1'('#skF_9',B_916),'#skF_8')
      | ~ v1_tops_2('#skF_9','#skF_8')
      | ~ l1_pre_topc('#skF_8')
      | r1_tarski('#skF_9',B_916)
      | ~ r1_tarski('#skF_1'('#skF_9',B_916),u1_struct_0('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_78,c_22536])).

tff(c_22562,plain,(
    ! [B_918] :
      ( v3_pre_topc('#skF_1'('#skF_9',B_918),'#skF_8')
      | r1_tarski('#skF_9',B_918)
      | ~ r1_tarski('#skF_1'('#skF_9',B_918),u1_struct_0('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_76,c_22552])).

tff(c_22570,plain,(
    ! [B_74] :
      ( v3_pre_topc('#skF_1'('#skF_9',B_74),'#skF_8')
      | ~ r1_tarski('#skF_9',k1_zfmisc_1(u1_struct_0('#skF_8')))
      | r1_tarski('#skF_9',B_74) ) ),
    inference(resolution,[status(thm)],[c_172,c_22562])).

tff(c_22577,plain,(
    ! [B_919] :
      ( v3_pre_topc('#skF_1'('#skF_9',B_919),'#skF_8')
      | r1_tarski('#skF_9',B_919) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_22570])).

tff(c_257,plain,(
    ! [B_96,A_97] :
      ( r2_hidden(B_96,u1_pre_topc(A_97))
      | ~ v3_pre_topc(B_96,A_97)
      | ~ m1_subset_1(B_96,k1_zfmisc_1(u1_struct_0(A_97)))
      | ~ l1_pre_topc(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_268,plain,(
    ! [A_98,A_99] :
      ( r2_hidden(A_98,u1_pre_topc(A_99))
      | ~ v3_pre_topc(A_98,A_99)
      | ~ l1_pre_topc(A_99)
      | ~ r1_tarski(A_98,u1_struct_0(A_99)) ) ),
    inference(resolution,[status(thm)],[c_24,c_257])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_3729,plain,(
    ! [A_334,A_335] :
      ( r1_tarski(A_334,u1_pre_topc(A_335))
      | ~ v3_pre_topc('#skF_1'(A_334,u1_pre_topc(A_335)),A_335)
      | ~ l1_pre_topc(A_335)
      | ~ r1_tarski('#skF_1'(A_334,u1_pre_topc(A_335)),u1_struct_0(A_335)) ) ),
    inference(resolution,[status(thm)],[c_268,c_4])).

tff(c_3752,plain,(
    ! [A_73,A_335] :
      ( ~ v3_pre_topc('#skF_1'(A_73,u1_pre_topc(A_335)),A_335)
      | ~ l1_pre_topc(A_335)
      | ~ r1_tarski(A_73,k1_zfmisc_1(u1_struct_0(A_335)))
      | r1_tarski(A_73,u1_pre_topc(A_335)) ) ),
    inference(resolution,[status(thm)],[c_172,c_3729])).

tff(c_22581,plain,
    ( ~ l1_pre_topc('#skF_8')
    | ~ r1_tarski('#skF_9',k1_zfmisc_1(u1_struct_0('#skF_8')))
    | r1_tarski('#skF_9',u1_pre_topc('#skF_8')) ),
    inference(resolution,[status(thm)],[c_22577,c_3752])).

tff(c_22588,plain,(
    r1_tarski('#skF_9',u1_pre_topc('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_80,c_22581])).

tff(c_22590,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5053,c_22588])).

tff(c_22592,plain,(
    r1_tarski('#skF_9',u1_pre_topc('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_5052])).

tff(c_1395,plain,(
    ! [A_204,B_205] :
      ( r2_hidden(k5_setfam_1(u1_struct_0(A_204),B_205),u1_pre_topc(A_204))
      | ~ r1_tarski(B_205,u1_pre_topc(A_204))
      | ~ m1_subset_1(B_205,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_204))))
      | ~ v2_pre_topc(A_204)
      | ~ l1_pre_topc(A_204) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_24614,plain,(
    ! [A_992,B_993,B_994] :
      ( r2_hidden(k5_setfam_1(u1_struct_0(A_992),B_993),B_994)
      | ~ r1_tarski(u1_pre_topc(A_992),B_994)
      | ~ r1_tarski(B_993,u1_pre_topc(A_992))
      | ~ m1_subset_1(B_993,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_992))))
      | ~ v2_pre_topc(A_992)
      | ~ l1_pre_topc(A_992) ) ),
    inference(resolution,[status(thm)],[c_1395,c_2])).

tff(c_24630,plain,(
    ! [B_994] :
      ( r2_hidden(k5_setfam_1(u1_struct_0('#skF_8'),'#skF_9'),B_994)
      | ~ r1_tarski(u1_pre_topc('#skF_8'),B_994)
      | ~ r1_tarski('#skF_9',u1_pre_topc('#skF_8'))
      | ~ v2_pre_topc('#skF_8')
      | ~ l1_pre_topc('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_78,c_24614])).

tff(c_24640,plain,(
    ! [B_995] :
      ( r2_hidden(k5_setfam_1(u1_struct_0('#skF_8'),'#skF_9'),B_995)
      | ~ r1_tarski(u1_pre_topc('#skF_8'),B_995) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_82,c_22592,c_24630])).

tff(c_20,plain,(
    ! [A_11,B_12] :
      ( m1_subset_1(k5_setfam_1(A_11,B_12),k1_zfmisc_1(A_11))
      | ~ m1_subset_1(B_12,k1_zfmisc_1(k1_zfmisc_1(A_11))) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_221,plain,(
    ! [A_90,B_12] :
      ( v3_pre_topc(k5_setfam_1(u1_struct_0(A_90),B_12),A_90)
      | ~ r2_hidden(k5_setfam_1(u1_struct_0(A_90),B_12),u1_pre_topc(A_90))
      | ~ l1_pre_topc(A_90)
      | ~ m1_subset_1(B_12,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_90)))) ) ),
    inference(resolution,[status(thm)],[c_20,c_212])).

tff(c_24644,plain,
    ( v3_pre_topc(k5_setfam_1(u1_struct_0('#skF_8'),'#skF_9'),'#skF_8')
    | ~ l1_pre_topc('#skF_8')
    | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_8'))))
    | ~ r1_tarski(u1_pre_topc('#skF_8'),u1_pre_topc('#skF_8')) ),
    inference(resolution,[status(thm)],[c_24640,c_221])).

tff(c_24659,plain,(
    v3_pre_topc(k5_setfam_1(u1_struct_0('#skF_8'),'#skF_9'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_78,c_80,c_24644])).

tff(c_24661,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_24659])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:49:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 16.56/7.71  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 16.56/7.72  
% 16.56/7.72  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 16.56/7.72  %$ v3_pre_topc > v1_tops_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k5_setfam_1 > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_5 > #skF_4 > #skF_3 > #skF_9 > #skF_8 > #skF_2 > #skF_7 > #skF_1 > #skF_6
% 16.56/7.72  
% 16.56/7.72  %Foreground sorts:
% 16.56/7.72  
% 16.56/7.72  
% 16.56/7.72  %Background operators:
% 16.56/7.72  
% 16.56/7.72  
% 16.56/7.72  %Foreground operators:
% 16.56/7.72  tff('#skF_5', type, '#skF_5': $i > $i).
% 16.56/7.72  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 16.56/7.72  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 16.56/7.72  tff('#skF_4', type, '#skF_4': $i > $i).
% 16.56/7.72  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 16.56/7.72  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 16.56/7.72  tff(v1_tops_2, type, v1_tops_2: ($i * $i) > $o).
% 16.56/7.72  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 16.56/7.72  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 16.56/7.72  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 16.56/7.72  tff('#skF_9', type, '#skF_9': $i).
% 16.56/7.72  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 16.56/7.72  tff(k5_setfam_1, type, k5_setfam_1: ($i * $i) > $i).
% 16.56/7.72  tff('#skF_8', type, '#skF_8': $i).
% 16.56/7.72  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 16.56/7.72  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 16.56/7.72  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 16.56/7.72  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 16.56/7.72  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 16.56/7.72  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 16.56/7.72  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 16.56/7.72  tff('#skF_6', type, '#skF_6': $i > $i).
% 16.56/7.72  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 16.56/7.72  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 16.56/7.72  
% 16.80/7.73  tff(f_107, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (v1_tops_2(B, A) => v3_pre_topc(k5_setfam_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_tops_2)).
% 16.80/7.73  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 16.80/7.73  tff(f_47, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 16.80/7.73  tff(f_39, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 16.80/7.73  tff(f_81, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> r2_hidden(B, u1_pre_topc(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_pre_topc)).
% 16.80/7.73  tff(f_95, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (v1_tops_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(C, B) => v3_pre_topc(C, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tops_2)).
% 16.80/7.73  tff(f_72, axiom, (![A]: (l1_pre_topc(A) => (v2_pre_topc(A) <=> ((r2_hidden(u1_struct_0(A), u1_pre_topc(A)) & (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (r1_tarski(B, u1_pre_topc(A)) => r2_hidden(k5_setfam_1(u1_struct_0(A), B), u1_pre_topc(A)))))) & (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r2_hidden(B, u1_pre_topc(A)) & r2_hidden(C, u1_pre_topc(A))) => r2_hidden(k9_subset_1(u1_struct_0(A), B, C), u1_pre_topc(A))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_pre_topc)).
% 16.80/7.73  tff(f_43, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k5_setfam_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_setfam_1)).
% 16.80/7.73  tff(c_74, plain, (~v3_pre_topc(k5_setfam_1(u1_struct_0('#skF_8'), '#skF_9'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_107])).
% 16.80/7.73  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 16.80/7.73  tff(c_105, plain, (![A_53, B_54]: (~r2_hidden('#skF_1'(A_53, B_54), B_54) | r1_tarski(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_32])).
% 16.80/7.73  tff(c_114, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_105])).
% 16.80/7.73  tff(c_78, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_8'))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 16.80/7.73  tff(c_80, plain, (l1_pre_topc('#skF_8')), inference(cnfTransformation, [status(thm)], [f_107])).
% 16.80/7.73  tff(c_82, plain, (v2_pre_topc('#skF_8')), inference(cnfTransformation, [status(thm)], [f_107])).
% 16.80/7.73  tff(c_84, plain, (![A_45, B_46]: (r1_tarski(A_45, B_46) | ~m1_subset_1(A_45, k1_zfmisc_1(B_46)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 16.80/7.73  tff(c_88, plain, (r1_tarski('#skF_9', k1_zfmisc_1(u1_struct_0('#skF_8')))), inference(resolution, [status(thm)], [c_78, c_84])).
% 16.80/7.73  tff(c_117, plain, (![C_56, B_57, A_58]: (r2_hidden(C_56, B_57) | ~r2_hidden(C_56, A_58) | ~r1_tarski(A_58, B_57))), inference(cnfTransformation, [status(thm)], [f_32])).
% 16.80/7.73  tff(c_159, plain, (![A_73, B_74, B_75]: (r2_hidden('#skF_1'(A_73, B_74), B_75) | ~r1_tarski(A_73, B_75) | r1_tarski(A_73, B_74))), inference(resolution, [status(thm)], [c_6, c_117])).
% 16.80/7.73  tff(c_8, plain, (![C_10, A_6]: (r1_tarski(C_10, A_6) | ~r2_hidden(C_10, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 16.80/7.73  tff(c_172, plain, (![A_73, B_74, A_6]: (r1_tarski('#skF_1'(A_73, B_74), A_6) | ~r1_tarski(A_73, k1_zfmisc_1(A_6)) | r1_tarski(A_73, B_74))), inference(resolution, [status(thm)], [c_159, c_8])).
% 16.80/7.73  tff(c_122, plain, (![A_1, B_2, B_57]: (r2_hidden('#skF_1'(A_1, B_2), B_57) | ~r1_tarski(A_1, B_57) | r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_6, c_117])).
% 16.80/7.73  tff(c_24, plain, (![A_13, B_14]: (m1_subset_1(A_13, k1_zfmisc_1(B_14)) | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_47])).
% 16.80/7.73  tff(c_212, plain, (![B_89, A_90]: (v3_pre_topc(B_89, A_90) | ~r2_hidden(B_89, u1_pre_topc(A_90)) | ~m1_subset_1(B_89, k1_zfmisc_1(u1_struct_0(A_90))) | ~l1_pre_topc(A_90))), inference(cnfTransformation, [status(thm)], [f_81])).
% 16.80/7.73  tff(c_223, plain, (![A_91, A_92]: (v3_pre_topc(A_91, A_92) | ~r2_hidden(A_91, u1_pre_topc(A_92)) | ~l1_pre_topc(A_92) | ~r1_tarski(A_91, u1_struct_0(A_92)))), inference(resolution, [status(thm)], [c_24, c_212])).
% 16.80/7.73  tff(c_4853, plain, (![A_409, B_410, A_411]: (v3_pre_topc('#skF_1'(A_409, B_410), A_411) | ~l1_pre_topc(A_411) | ~r1_tarski('#skF_1'(A_409, B_410), u1_struct_0(A_411)) | ~r1_tarski(A_409, u1_pre_topc(A_411)) | r1_tarski(A_409, B_410))), inference(resolution, [status(thm)], [c_122, c_223])).
% 16.80/7.73  tff(c_4910, plain, (![A_414, B_415, A_416]: (v3_pre_topc('#skF_1'(A_414, B_415), A_416) | ~l1_pre_topc(A_416) | ~r1_tarski(A_414, u1_pre_topc(A_416)) | ~r1_tarski(A_414, k1_zfmisc_1(u1_struct_0(A_416))) | r1_tarski(A_414, B_415))), inference(resolution, [status(thm)], [c_172, c_4853])).
% 16.80/7.73  tff(c_5000, plain, (![B_415]: (v3_pre_topc('#skF_1'('#skF_9', B_415), '#skF_8') | ~l1_pre_topc('#skF_8') | ~r1_tarski('#skF_9', u1_pre_topc('#skF_8')) | r1_tarski('#skF_9', B_415))), inference(resolution, [status(thm)], [c_88, c_4910])).
% 16.80/7.73  tff(c_5052, plain, (![B_415]: (v3_pre_topc('#skF_1'('#skF_9', B_415), '#skF_8') | ~r1_tarski('#skF_9', u1_pre_topc('#skF_8')) | r1_tarski('#skF_9', B_415))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_5000])).
% 16.80/7.73  tff(c_5053, plain, (~r1_tarski('#skF_9', u1_pre_topc('#skF_8'))), inference(splitLeft, [status(thm)], [c_5052])).
% 16.80/7.73  tff(c_76, plain, (v1_tops_2('#skF_9', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_107])).
% 16.80/7.73  tff(c_2452, plain, (![C_255, A_256, B_257]: (v3_pre_topc(C_255, A_256) | ~r2_hidden(C_255, B_257) | ~m1_subset_1(C_255, k1_zfmisc_1(u1_struct_0(A_256))) | ~v1_tops_2(B_257, A_256) | ~m1_subset_1(B_257, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_256)))) | ~l1_pre_topc(A_256))), inference(cnfTransformation, [status(thm)], [f_95])).
% 16.80/7.73  tff(c_8659, plain, (![A_578, B_579, A_580]: (v3_pre_topc('#skF_1'(A_578, B_579), A_580) | ~m1_subset_1('#skF_1'(A_578, B_579), k1_zfmisc_1(u1_struct_0(A_580))) | ~v1_tops_2(A_578, A_580) | ~m1_subset_1(A_578, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_580)))) | ~l1_pre_topc(A_580) | r1_tarski(A_578, B_579))), inference(resolution, [status(thm)], [c_6, c_2452])).
% 16.80/7.73  tff(c_22536, plain, (![A_915, B_916, A_917]: (v3_pre_topc('#skF_1'(A_915, B_916), A_917) | ~v1_tops_2(A_915, A_917) | ~m1_subset_1(A_915, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_917)))) | ~l1_pre_topc(A_917) | r1_tarski(A_915, B_916) | ~r1_tarski('#skF_1'(A_915, B_916), u1_struct_0(A_917)))), inference(resolution, [status(thm)], [c_24, c_8659])).
% 16.80/7.73  tff(c_22552, plain, (![B_916]: (v3_pre_topc('#skF_1'('#skF_9', B_916), '#skF_8') | ~v1_tops_2('#skF_9', '#skF_8') | ~l1_pre_topc('#skF_8') | r1_tarski('#skF_9', B_916) | ~r1_tarski('#skF_1'('#skF_9', B_916), u1_struct_0('#skF_8')))), inference(resolution, [status(thm)], [c_78, c_22536])).
% 16.80/7.73  tff(c_22562, plain, (![B_918]: (v3_pre_topc('#skF_1'('#skF_9', B_918), '#skF_8') | r1_tarski('#skF_9', B_918) | ~r1_tarski('#skF_1'('#skF_9', B_918), u1_struct_0('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_76, c_22552])).
% 16.80/7.73  tff(c_22570, plain, (![B_74]: (v3_pre_topc('#skF_1'('#skF_9', B_74), '#skF_8') | ~r1_tarski('#skF_9', k1_zfmisc_1(u1_struct_0('#skF_8'))) | r1_tarski('#skF_9', B_74))), inference(resolution, [status(thm)], [c_172, c_22562])).
% 16.80/7.73  tff(c_22577, plain, (![B_919]: (v3_pre_topc('#skF_1'('#skF_9', B_919), '#skF_8') | r1_tarski('#skF_9', B_919))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_22570])).
% 16.80/7.73  tff(c_257, plain, (![B_96, A_97]: (r2_hidden(B_96, u1_pre_topc(A_97)) | ~v3_pre_topc(B_96, A_97) | ~m1_subset_1(B_96, k1_zfmisc_1(u1_struct_0(A_97))) | ~l1_pre_topc(A_97))), inference(cnfTransformation, [status(thm)], [f_81])).
% 16.80/7.73  tff(c_268, plain, (![A_98, A_99]: (r2_hidden(A_98, u1_pre_topc(A_99)) | ~v3_pre_topc(A_98, A_99) | ~l1_pre_topc(A_99) | ~r1_tarski(A_98, u1_struct_0(A_99)))), inference(resolution, [status(thm)], [c_24, c_257])).
% 16.80/7.73  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 16.80/7.73  tff(c_3729, plain, (![A_334, A_335]: (r1_tarski(A_334, u1_pre_topc(A_335)) | ~v3_pre_topc('#skF_1'(A_334, u1_pre_topc(A_335)), A_335) | ~l1_pre_topc(A_335) | ~r1_tarski('#skF_1'(A_334, u1_pre_topc(A_335)), u1_struct_0(A_335)))), inference(resolution, [status(thm)], [c_268, c_4])).
% 16.80/7.73  tff(c_3752, plain, (![A_73, A_335]: (~v3_pre_topc('#skF_1'(A_73, u1_pre_topc(A_335)), A_335) | ~l1_pre_topc(A_335) | ~r1_tarski(A_73, k1_zfmisc_1(u1_struct_0(A_335))) | r1_tarski(A_73, u1_pre_topc(A_335)))), inference(resolution, [status(thm)], [c_172, c_3729])).
% 16.80/7.73  tff(c_22581, plain, (~l1_pre_topc('#skF_8') | ~r1_tarski('#skF_9', k1_zfmisc_1(u1_struct_0('#skF_8'))) | r1_tarski('#skF_9', u1_pre_topc('#skF_8'))), inference(resolution, [status(thm)], [c_22577, c_3752])).
% 16.80/7.73  tff(c_22588, plain, (r1_tarski('#skF_9', u1_pre_topc('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_80, c_22581])).
% 16.80/7.73  tff(c_22590, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5053, c_22588])).
% 16.80/7.73  tff(c_22592, plain, (r1_tarski('#skF_9', u1_pre_topc('#skF_8'))), inference(splitRight, [status(thm)], [c_5052])).
% 16.80/7.73  tff(c_1395, plain, (![A_204, B_205]: (r2_hidden(k5_setfam_1(u1_struct_0(A_204), B_205), u1_pre_topc(A_204)) | ~r1_tarski(B_205, u1_pre_topc(A_204)) | ~m1_subset_1(B_205, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_204)))) | ~v2_pre_topc(A_204) | ~l1_pre_topc(A_204))), inference(cnfTransformation, [status(thm)], [f_72])).
% 16.80/7.73  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 16.80/7.73  tff(c_24614, plain, (![A_992, B_993, B_994]: (r2_hidden(k5_setfam_1(u1_struct_0(A_992), B_993), B_994) | ~r1_tarski(u1_pre_topc(A_992), B_994) | ~r1_tarski(B_993, u1_pre_topc(A_992)) | ~m1_subset_1(B_993, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_992)))) | ~v2_pre_topc(A_992) | ~l1_pre_topc(A_992))), inference(resolution, [status(thm)], [c_1395, c_2])).
% 16.80/7.73  tff(c_24630, plain, (![B_994]: (r2_hidden(k5_setfam_1(u1_struct_0('#skF_8'), '#skF_9'), B_994) | ~r1_tarski(u1_pre_topc('#skF_8'), B_994) | ~r1_tarski('#skF_9', u1_pre_topc('#skF_8')) | ~v2_pre_topc('#skF_8') | ~l1_pre_topc('#skF_8'))), inference(resolution, [status(thm)], [c_78, c_24614])).
% 16.80/7.73  tff(c_24640, plain, (![B_995]: (r2_hidden(k5_setfam_1(u1_struct_0('#skF_8'), '#skF_9'), B_995) | ~r1_tarski(u1_pre_topc('#skF_8'), B_995))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_82, c_22592, c_24630])).
% 16.80/7.73  tff(c_20, plain, (![A_11, B_12]: (m1_subset_1(k5_setfam_1(A_11, B_12), k1_zfmisc_1(A_11)) | ~m1_subset_1(B_12, k1_zfmisc_1(k1_zfmisc_1(A_11))))), inference(cnfTransformation, [status(thm)], [f_43])).
% 16.80/7.73  tff(c_221, plain, (![A_90, B_12]: (v3_pre_topc(k5_setfam_1(u1_struct_0(A_90), B_12), A_90) | ~r2_hidden(k5_setfam_1(u1_struct_0(A_90), B_12), u1_pre_topc(A_90)) | ~l1_pre_topc(A_90) | ~m1_subset_1(B_12, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_90)))))), inference(resolution, [status(thm)], [c_20, c_212])).
% 16.80/7.73  tff(c_24644, plain, (v3_pre_topc(k5_setfam_1(u1_struct_0('#skF_8'), '#skF_9'), '#skF_8') | ~l1_pre_topc('#skF_8') | ~m1_subset_1('#skF_9', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_8')))) | ~r1_tarski(u1_pre_topc('#skF_8'), u1_pre_topc('#skF_8'))), inference(resolution, [status(thm)], [c_24640, c_221])).
% 16.80/7.73  tff(c_24659, plain, (v3_pre_topc(k5_setfam_1(u1_struct_0('#skF_8'), '#skF_9'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_114, c_78, c_80, c_24644])).
% 16.80/7.73  tff(c_24661, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_24659])).
% 16.80/7.73  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 16.80/7.73  
% 16.80/7.73  Inference rules
% 16.80/7.73  ----------------------
% 16.80/7.74  #Ref     : 0
% 16.80/7.74  #Sup     : 6615
% 16.80/7.74  #Fact    : 0
% 16.80/7.74  #Define  : 0
% 16.80/7.74  #Split   : 45
% 16.80/7.74  #Chain   : 0
% 16.80/7.74  #Close   : 0
% 16.80/7.74  
% 16.80/7.74  Ordering : KBO
% 16.80/7.74  
% 16.80/7.74  Simplification rules
% 16.80/7.74  ----------------------
% 16.80/7.74  #Subsume      : 2061
% 16.80/7.74  #Demod        : 380
% 16.80/7.74  #Tautology    : 144
% 16.80/7.74  #SimpNegUnit  : 3
% 16.80/7.74  #BackRed      : 0
% 16.80/7.74  
% 16.80/7.74  #Partial instantiations: 0
% 16.80/7.74  #Strategies tried      : 1
% 16.80/7.74  
% 16.80/7.74  Timing (in seconds)
% 16.80/7.74  ----------------------
% 16.80/7.74  Preprocessing        : 0.33
% 16.80/7.74  Parsing              : 0.18
% 16.80/7.74  CNF conversion       : 0.03
% 16.80/7.74  Main loop            : 6.59
% 16.80/7.74  Inferencing          : 1.13
% 16.80/7.74  Reduction            : 1.17
% 16.80/7.74  Demodulation         : 0.71
% 16.80/7.74  BG Simplification    : 0.11
% 16.80/7.74  Subsumption          : 3.78
% 16.80/7.74  Abstraction          : 0.17
% 16.80/7.74  MUC search           : 0.00
% 16.80/7.74  Cooper               : 0.00
% 16.80/7.74  Total                : 6.95
% 16.80/7.74  Index Insertion      : 0.00
% 16.80/7.74  Index Deletion       : 0.00
% 16.80/7.74  Index Matching       : 0.00
% 16.80/7.74  BG Taut test         : 0.00
%------------------------------------------------------------------------------
