%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:05 EST 2020

% Result     : Theorem 4.01s
% Output     : CNFRefutation 4.01s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 199 expanded)
%              Number of leaves         :   31 (  88 expanded)
%              Depth                    :   21
%              Number of atoms          :  267 ( 753 expanded)
%              Number of equality atoms :   38 (  50 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_tex_2 > v2_tex_2 > v1_tops_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

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

tff(v1_tops_1,type,(
    v1_tops_1: ( $i * $i ) > $o )).

tff(v3_tex_2,type,(
    v3_tex_2: ( $i * $i ) > $o )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_120,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( ( v1_tops_1(B,A)
                & v2_tex_2(B,A) )
             => v3_tex_2(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tex_2)).

tff(f_84,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_tex_2)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_37,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k9_subset_1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_66,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> k2_pre_topc(A,B) = u1_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tops_3)).

tff(f_103,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tex_2(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( r1_tarski(C,B)
                 => k9_subset_1(u1_struct_0(A),B,k2_pre_topc(A,C)) = C ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_tex_2)).

tff(f_57,axiom,(
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

tff(c_38,plain,(
    ~ v3_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_44,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_40,plain,(
    v2_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_46,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_202,plain,(
    ! [A_76,B_77] :
      ( v2_tex_2('#skF_1'(A_76,B_77),A_76)
      | v3_tex_2(B_77,A_76)
      | ~ v2_tex_2(B_77,A_76)
      | ~ m1_subset_1(B_77,k1_zfmisc_1(u1_struct_0(A_76)))
      | ~ l1_pre_topc(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_204,plain,
    ( v2_tex_2('#skF_1'('#skF_3','#skF_4'),'#skF_3')
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_202])).

tff(c_210,plain,
    ( v2_tex_2('#skF_1'('#skF_3','#skF_4'),'#skF_3')
    | v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_40,c_204])).

tff(c_211,plain,(
    v2_tex_2('#skF_1'('#skF_3','#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_210])).

tff(c_213,plain,(
    ! [B_78,A_79] :
      ( r1_tarski(B_78,'#skF_1'(A_79,B_78))
      | v3_tex_2(B_78,A_79)
      | ~ v2_tex_2(B_78,A_79)
      | ~ m1_subset_1(B_78,k1_zfmisc_1(u1_struct_0(A_79)))
      | ~ l1_pre_topc(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_215,plain,
    ( r1_tarski('#skF_4','#skF_1'('#skF_3','#skF_4'))
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_213])).

tff(c_221,plain,
    ( r1_tarski('#skF_4','#skF_1'('#skF_3','#skF_4'))
    | v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_40,c_215])).

tff(c_222,plain,(
    r1_tarski('#skF_4','#skF_1'('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_221])).

tff(c_238,plain,(
    ! [A_85,B_86] :
      ( m1_subset_1('#skF_1'(A_85,B_86),k1_zfmisc_1(u1_struct_0(A_85)))
      | v3_tex_2(B_86,A_85)
      | ~ v2_tex_2(B_86,A_85)
      | ~ m1_subset_1(B_86,k1_zfmisc_1(u1_struct_0(A_85)))
      | ~ l1_pre_topc(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_6,plain,(
    ! [A_6,B_7,C_8] :
      ( k9_subset_1(A_6,B_7,C_8) = k3_xboole_0(B_7,C_8)
      | ~ m1_subset_1(C_8,k1_zfmisc_1(A_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_399,plain,(
    ! [A_112,B_113,B_114] :
      ( k9_subset_1(u1_struct_0(A_112),B_113,'#skF_1'(A_112,B_114)) = k3_xboole_0(B_113,'#skF_1'(A_112,B_114))
      | v3_tex_2(B_114,A_112)
      | ~ v2_tex_2(B_114,A_112)
      | ~ m1_subset_1(B_114,k1_zfmisc_1(u1_struct_0(A_112)))
      | ~ l1_pre_topc(A_112) ) ),
    inference(resolution,[status(thm)],[c_238,c_6])).

tff(c_405,plain,(
    ! [B_113] :
      ( k9_subset_1(u1_struct_0('#skF_3'),B_113,'#skF_1'('#skF_3','#skF_4')) = k3_xboole_0(B_113,'#skF_1'('#skF_3','#skF_4'))
      | v3_tex_2('#skF_4','#skF_3')
      | ~ v2_tex_2('#skF_4','#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_44,c_399])).

tff(c_413,plain,(
    ! [B_113] :
      ( k9_subset_1(u1_struct_0('#skF_3'),B_113,'#skF_1'('#skF_3','#skF_4')) = k3_xboole_0(B_113,'#skF_1'('#skF_3','#skF_4'))
      | v3_tex_2('#skF_4','#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_40,c_405])).

tff(c_416,plain,(
    ! [B_115] : k9_subset_1(u1_struct_0('#skF_3'),B_115,'#skF_1'('#skF_3','#skF_4')) = k3_xboole_0(B_115,'#skF_1'('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_413])).

tff(c_8,plain,(
    ! [A_9] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_53,plain,(
    ! [A_47,B_48,C_49] :
      ( k9_subset_1(A_47,B_48,B_48) = B_48
      | ~ m1_subset_1(C_49,k1_zfmisc_1(A_47)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_59,plain,(
    ! [A_9,B_48] : k9_subset_1(A_9,B_48,B_48) = B_48 ),
    inference(resolution,[status(thm)],[c_8,c_53])).

tff(c_423,plain,(
    k3_xboole_0('#skF_1'('#skF_3','#skF_4'),'#skF_1'('#skF_3','#skF_4')) = '#skF_1'('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_416,c_59])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k3_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_439,plain,(
    r1_tarski('#skF_1'('#skF_3','#skF_4'),'#skF_1'('#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_423,c_2])).

tff(c_184,plain,(
    ! [A_73,B_74] :
      ( '#skF_1'(A_73,B_74) != B_74
      | v3_tex_2(B_74,A_73)
      | ~ v2_tex_2(B_74,A_73)
      | ~ m1_subset_1(B_74,k1_zfmisc_1(u1_struct_0(A_73)))
      | ~ l1_pre_topc(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_187,plain,
    ( '#skF_1'('#skF_3','#skF_4') != '#skF_4'
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_184])).

tff(c_194,plain,
    ( '#skF_1'('#skF_3','#skF_4') != '#skF_4'
    | v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_40,c_187])).

tff(c_195,plain,(
    '#skF_1'('#skF_3','#skF_4') != '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_194])).

tff(c_24,plain,(
    ! [A_23,B_29] :
      ( m1_subset_1('#skF_1'(A_23,B_29),k1_zfmisc_1(u1_struct_0(A_23)))
      | v3_tex_2(B_29,A_23)
      | ~ v2_tex_2(B_29,A_23)
      | ~ m1_subset_1(B_29,k1_zfmisc_1(u1_struct_0(A_23)))
      | ~ l1_pre_topc(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_50,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_48,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_42,plain,(
    v1_tops_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_149,plain,(
    ! [A_66,B_67] :
      ( k2_pre_topc(A_66,B_67) = u1_struct_0(A_66)
      | ~ v1_tops_1(B_67,A_66)
      | ~ m1_subset_1(B_67,k1_zfmisc_1(u1_struct_0(A_66)))
      | ~ l1_pre_topc(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_152,plain,
    ( k2_pre_topc('#skF_3','#skF_4') = u1_struct_0('#skF_3')
    | ~ v1_tops_1('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_149])).

tff(c_159,plain,(
    k2_pre_topc('#skF_3','#skF_4') = u1_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_42,c_152])).

tff(c_492,plain,(
    ! [A_120,B_121,C_122] :
      ( k9_subset_1(u1_struct_0(A_120),B_121,k2_pre_topc(A_120,C_122)) = C_122
      | ~ r1_tarski(C_122,B_121)
      | ~ m1_subset_1(C_122,k1_zfmisc_1(u1_struct_0(A_120)))
      | ~ v2_tex_2(B_121,A_120)
      | ~ m1_subset_1(B_121,k1_zfmisc_1(u1_struct_0(A_120)))
      | ~ l1_pre_topc(A_120)
      | ~ v2_pre_topc(A_120)
      | v2_struct_0(A_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_498,plain,(
    ! [B_121] :
      ( k9_subset_1(u1_struct_0('#skF_3'),B_121,k2_pre_topc('#skF_3','#skF_4')) = '#skF_4'
      | ~ r1_tarski('#skF_4',B_121)
      | ~ v2_tex_2(B_121,'#skF_3')
      | ~ m1_subset_1(B_121,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_44,c_492])).

tff(c_506,plain,(
    ! [B_121] :
      ( k9_subset_1(u1_struct_0('#skF_3'),B_121,u1_struct_0('#skF_3')) = '#skF_4'
      | ~ r1_tarski('#skF_4',B_121)
      | ~ v2_tex_2(B_121,'#skF_3')
      | ~ m1_subset_1(B_121,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_159,c_498])).

tff(c_509,plain,(
    ! [B_123] :
      ( k9_subset_1(u1_struct_0('#skF_3'),B_123,u1_struct_0('#skF_3')) = '#skF_4'
      | ~ r1_tarski('#skF_4',B_123)
      | ~ v2_tex_2(B_123,'#skF_3')
      | ~ m1_subset_1(B_123,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_506])).

tff(c_517,plain,(
    ! [B_29] :
      ( k9_subset_1(u1_struct_0('#skF_3'),'#skF_1'('#skF_3',B_29),u1_struct_0('#skF_3')) = '#skF_4'
      | ~ r1_tarski('#skF_4','#skF_1'('#skF_3',B_29))
      | ~ v2_tex_2('#skF_1'('#skF_3',B_29),'#skF_3')
      | v3_tex_2(B_29,'#skF_3')
      | ~ v2_tex_2(B_29,'#skF_3')
      | ~ m1_subset_1(B_29,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_24,c_509])).

tff(c_531,plain,(
    ! [B_29] :
      ( k9_subset_1(u1_struct_0('#skF_3'),'#skF_1'('#skF_3',B_29),u1_struct_0('#skF_3')) = '#skF_4'
      | ~ r1_tarski('#skF_4','#skF_1'('#skF_3',B_29))
      | ~ v2_tex_2('#skF_1'('#skF_3',B_29),'#skF_3')
      | v3_tex_2(B_29,'#skF_3')
      | ~ v2_tex_2(B_29,'#skF_3')
      | ~ m1_subset_1(B_29,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_517])).

tff(c_270,plain,(
    ! [C_87,A_88,B_89] :
      ( v1_tops_1(C_87,A_88)
      | ~ r1_tarski(B_89,C_87)
      | ~ v1_tops_1(B_89,A_88)
      | ~ m1_subset_1(C_87,k1_zfmisc_1(u1_struct_0(A_88)))
      | ~ m1_subset_1(B_89,k1_zfmisc_1(u1_struct_0(A_88)))
      | ~ l1_pre_topc(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_367,plain,(
    ! [A_101] :
      ( v1_tops_1('#skF_1'('#skF_3','#skF_4'),A_101)
      | ~ v1_tops_1('#skF_4',A_101)
      | ~ m1_subset_1('#skF_1'('#skF_3','#skF_4'),k1_zfmisc_1(u1_struct_0(A_101)))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_101)))
      | ~ l1_pre_topc(A_101) ) ),
    inference(resolution,[status(thm)],[c_222,c_270])).

tff(c_371,plain,
    ( v1_tops_1('#skF_1'('#skF_3','#skF_4'),'#skF_3')
    | ~ v1_tops_1('#skF_4','#skF_3')
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_367])).

tff(c_374,plain,
    ( v1_tops_1('#skF_1'('#skF_3','#skF_4'),'#skF_3')
    | v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_40,c_42,c_371])).

tff(c_375,plain,(
    v1_tops_1('#skF_1'('#skF_3','#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_374])).

tff(c_16,plain,(
    ! [A_20,B_22] :
      ( k2_pre_topc(A_20,B_22) = u1_struct_0(A_20)
      | ~ v1_tops_1(B_22,A_20)
      | ~ m1_subset_1(B_22,k1_zfmisc_1(u1_struct_0(A_20)))
      | ~ l1_pre_topc(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_387,plain,(
    ! [A_108,B_109] :
      ( k2_pre_topc(A_108,'#skF_1'(A_108,B_109)) = u1_struct_0(A_108)
      | ~ v1_tops_1('#skF_1'(A_108,B_109),A_108)
      | v3_tex_2(B_109,A_108)
      | ~ v2_tex_2(B_109,A_108)
      | ~ m1_subset_1(B_109,k1_zfmisc_1(u1_struct_0(A_108)))
      | ~ l1_pre_topc(A_108) ) ),
    inference(resolution,[status(thm)],[c_238,c_16])).

tff(c_389,plain,
    ( k2_pre_topc('#skF_3','#skF_1'('#skF_3','#skF_4')) = u1_struct_0('#skF_3')
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_375,c_387])).

tff(c_392,plain,
    ( k2_pre_topc('#skF_3','#skF_1'('#skF_3','#skF_4')) = u1_struct_0('#skF_3')
    | v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_40,c_389])).

tff(c_393,plain,(
    k2_pre_topc('#skF_3','#skF_1'('#skF_3','#skF_4')) = u1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_392])).

tff(c_921,plain,(
    ! [A_193,B_194,B_195] :
      ( k9_subset_1(u1_struct_0(A_193),B_194,k2_pre_topc(A_193,'#skF_1'(A_193,B_195))) = '#skF_1'(A_193,B_195)
      | ~ r1_tarski('#skF_1'(A_193,B_195),B_194)
      | ~ v2_tex_2(B_194,A_193)
      | ~ m1_subset_1(B_194,k1_zfmisc_1(u1_struct_0(A_193)))
      | ~ v2_pre_topc(A_193)
      | v2_struct_0(A_193)
      | v3_tex_2(B_195,A_193)
      | ~ v2_tex_2(B_195,A_193)
      | ~ m1_subset_1(B_195,k1_zfmisc_1(u1_struct_0(A_193)))
      | ~ l1_pre_topc(A_193) ) ),
    inference(resolution,[status(thm)],[c_24,c_492])).

tff(c_937,plain,(
    ! [B_194] :
      ( k9_subset_1(u1_struct_0('#skF_3'),B_194,u1_struct_0('#skF_3')) = '#skF_1'('#skF_3','#skF_4')
      | ~ r1_tarski('#skF_1'('#skF_3','#skF_4'),B_194)
      | ~ v2_tex_2(B_194,'#skF_3')
      | ~ m1_subset_1(B_194,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | v3_tex_2('#skF_4','#skF_3')
      | ~ v2_tex_2('#skF_4','#skF_3')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_393,c_921])).

tff(c_947,plain,(
    ! [B_194] :
      ( k9_subset_1(u1_struct_0('#skF_3'),B_194,u1_struct_0('#skF_3')) = '#skF_1'('#skF_3','#skF_4')
      | ~ r1_tarski('#skF_1'('#skF_3','#skF_4'),B_194)
      | ~ v2_tex_2(B_194,'#skF_3')
      | ~ m1_subset_1(B_194,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0('#skF_3')
      | v3_tex_2('#skF_4','#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_40,c_48,c_937])).

tff(c_949,plain,(
    ! [B_196] :
      ( k9_subset_1(u1_struct_0('#skF_3'),B_196,u1_struct_0('#skF_3')) = '#skF_1'('#skF_3','#skF_4')
      | ~ r1_tarski('#skF_1'('#skF_3','#skF_4'),B_196)
      | ~ v2_tex_2(B_196,'#skF_3')
      | ~ m1_subset_1(B_196,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_50,c_947])).

tff(c_957,plain,(
    ! [B_29] :
      ( k9_subset_1(u1_struct_0('#skF_3'),'#skF_1'('#skF_3',B_29),u1_struct_0('#skF_3')) = '#skF_1'('#skF_3','#skF_4')
      | ~ r1_tarski('#skF_1'('#skF_3','#skF_4'),'#skF_1'('#skF_3',B_29))
      | ~ v2_tex_2('#skF_1'('#skF_3',B_29),'#skF_3')
      | v3_tex_2(B_29,'#skF_3')
      | ~ v2_tex_2(B_29,'#skF_3')
      | ~ m1_subset_1(B_29,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_24,c_949])).

tff(c_995,plain,(
    ! [B_199] :
      ( k9_subset_1(u1_struct_0('#skF_3'),'#skF_1'('#skF_3',B_199),u1_struct_0('#skF_3')) = '#skF_1'('#skF_3','#skF_4')
      | ~ r1_tarski('#skF_1'('#skF_3','#skF_4'),'#skF_1'('#skF_3',B_199))
      | ~ v2_tex_2('#skF_1'('#skF_3',B_199),'#skF_3')
      | v3_tex_2(B_199,'#skF_3')
      | ~ v2_tex_2(B_199,'#skF_3')
      | ~ m1_subset_1(B_199,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_957])).

tff(c_1007,plain,(
    ! [B_29] :
      ( '#skF_1'('#skF_3','#skF_4') = '#skF_4'
      | ~ r1_tarski('#skF_1'('#skF_3','#skF_4'),'#skF_1'('#skF_3',B_29))
      | ~ v2_tex_2('#skF_1'('#skF_3',B_29),'#skF_3')
      | v3_tex_2(B_29,'#skF_3')
      | ~ v2_tex_2(B_29,'#skF_3')
      | ~ m1_subset_1(B_29,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ r1_tarski('#skF_4','#skF_1'('#skF_3',B_29))
      | ~ v2_tex_2('#skF_1'('#skF_3',B_29),'#skF_3')
      | v3_tex_2(B_29,'#skF_3')
      | ~ v2_tex_2(B_29,'#skF_3')
      | ~ m1_subset_1(B_29,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_531,c_995])).

tff(c_1085,plain,(
    ! [B_212] :
      ( ~ r1_tarski('#skF_1'('#skF_3','#skF_4'),'#skF_1'('#skF_3',B_212))
      | ~ v2_tex_2('#skF_1'('#skF_3',B_212),'#skF_3')
      | v3_tex_2(B_212,'#skF_3')
      | ~ v2_tex_2(B_212,'#skF_3')
      | ~ m1_subset_1(B_212,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ r1_tarski('#skF_4','#skF_1'('#skF_3',B_212))
      | ~ v2_tex_2('#skF_1'('#skF_3',B_212),'#skF_3')
      | v3_tex_2(B_212,'#skF_3')
      | ~ v2_tex_2(B_212,'#skF_3')
      | ~ m1_subset_1(B_212,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_195,c_1007])).

tff(c_1092,plain,
    ( ~ r1_tarski('#skF_4','#skF_1'('#skF_3','#skF_4'))
    | ~ v2_tex_2('#skF_1'('#skF_3','#skF_4'),'#skF_3')
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_439,c_1085])).

tff(c_1099,plain,(
    v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_40,c_211,c_222,c_1092])).

tff(c_1101,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_1099])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.34  % Computer   : n009.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 12:58:26 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.01/1.71  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.01/1.72  
% 4.01/1.72  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.01/1.72  %$ v3_tex_2 > v2_tex_2 > v1_tops_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 4.01/1.72  
% 4.01/1.72  %Foreground sorts:
% 4.01/1.72  
% 4.01/1.72  
% 4.01/1.72  %Background operators:
% 4.01/1.72  
% 4.01/1.72  
% 4.01/1.72  %Foreground operators:
% 4.01/1.72  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.01/1.72  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.01/1.72  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.01/1.72  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.01/1.72  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.01/1.72  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.01/1.72  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 4.01/1.72  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 4.01/1.72  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 4.01/1.72  tff('#skF_3', type, '#skF_3': $i).
% 4.01/1.72  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.01/1.72  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.01/1.72  tff('#skF_4', type, '#skF_4': $i).
% 4.01/1.72  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.01/1.72  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.01/1.72  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.01/1.72  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.01/1.72  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.01/1.72  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.01/1.72  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 4.01/1.72  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 4.01/1.72  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.01/1.72  
% 4.01/1.74  tff(f_120, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v1_tops_1(B, A) & v2_tex_2(B, A)) => v3_tex_2(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_tex_2)).
% 4.01/1.74  tff(f_84, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> (v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(C, A) & r1_tarski(B, C)) => (B = C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_tex_2)).
% 4.01/1.74  tff(f_35, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 4.01/1.74  tff(f_37, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 4.01/1.74  tff(f_31, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k9_subset_1)).
% 4.01/1.74  tff(f_27, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 4.01/1.74  tff(f_66, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tops_3)).
% 4.01/1.74  tff(f_103, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(C, B) => (k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, C)) = C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_tex_2)).
% 4.01/1.74  tff(f_57, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v1_tops_1(B, A) & r1_tarski(B, C)) => v1_tops_1(C, A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_tops_1)).
% 4.01/1.74  tff(c_38, plain, (~v3_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.01/1.74  tff(c_44, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.01/1.74  tff(c_40, plain, (v2_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.01/1.74  tff(c_46, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.01/1.74  tff(c_202, plain, (![A_76, B_77]: (v2_tex_2('#skF_1'(A_76, B_77), A_76) | v3_tex_2(B_77, A_76) | ~v2_tex_2(B_77, A_76) | ~m1_subset_1(B_77, k1_zfmisc_1(u1_struct_0(A_76))) | ~l1_pre_topc(A_76))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.01/1.74  tff(c_204, plain, (v2_tex_2('#skF_1'('#skF_3', '#skF_4'), '#skF_3') | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_44, c_202])).
% 4.01/1.74  tff(c_210, plain, (v2_tex_2('#skF_1'('#skF_3', '#skF_4'), '#skF_3') | v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_40, c_204])).
% 4.01/1.74  tff(c_211, plain, (v2_tex_2('#skF_1'('#skF_3', '#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_38, c_210])).
% 4.01/1.74  tff(c_213, plain, (![B_78, A_79]: (r1_tarski(B_78, '#skF_1'(A_79, B_78)) | v3_tex_2(B_78, A_79) | ~v2_tex_2(B_78, A_79) | ~m1_subset_1(B_78, k1_zfmisc_1(u1_struct_0(A_79))) | ~l1_pre_topc(A_79))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.01/1.74  tff(c_215, plain, (r1_tarski('#skF_4', '#skF_1'('#skF_3', '#skF_4')) | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_44, c_213])).
% 4.01/1.74  tff(c_221, plain, (r1_tarski('#skF_4', '#skF_1'('#skF_3', '#skF_4')) | v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_40, c_215])).
% 4.01/1.74  tff(c_222, plain, (r1_tarski('#skF_4', '#skF_1'('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_38, c_221])).
% 4.01/1.74  tff(c_238, plain, (![A_85, B_86]: (m1_subset_1('#skF_1'(A_85, B_86), k1_zfmisc_1(u1_struct_0(A_85))) | v3_tex_2(B_86, A_85) | ~v2_tex_2(B_86, A_85) | ~m1_subset_1(B_86, k1_zfmisc_1(u1_struct_0(A_85))) | ~l1_pre_topc(A_85))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.01/1.74  tff(c_6, plain, (![A_6, B_7, C_8]: (k9_subset_1(A_6, B_7, C_8)=k3_xboole_0(B_7, C_8) | ~m1_subset_1(C_8, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.01/1.74  tff(c_399, plain, (![A_112, B_113, B_114]: (k9_subset_1(u1_struct_0(A_112), B_113, '#skF_1'(A_112, B_114))=k3_xboole_0(B_113, '#skF_1'(A_112, B_114)) | v3_tex_2(B_114, A_112) | ~v2_tex_2(B_114, A_112) | ~m1_subset_1(B_114, k1_zfmisc_1(u1_struct_0(A_112))) | ~l1_pre_topc(A_112))), inference(resolution, [status(thm)], [c_238, c_6])).
% 4.01/1.74  tff(c_405, plain, (![B_113]: (k9_subset_1(u1_struct_0('#skF_3'), B_113, '#skF_1'('#skF_3', '#skF_4'))=k3_xboole_0(B_113, '#skF_1'('#skF_3', '#skF_4')) | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_44, c_399])).
% 4.01/1.74  tff(c_413, plain, (![B_113]: (k9_subset_1(u1_struct_0('#skF_3'), B_113, '#skF_1'('#skF_3', '#skF_4'))=k3_xboole_0(B_113, '#skF_1'('#skF_3', '#skF_4')) | v3_tex_2('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_40, c_405])).
% 4.01/1.74  tff(c_416, plain, (![B_115]: (k9_subset_1(u1_struct_0('#skF_3'), B_115, '#skF_1'('#skF_3', '#skF_4'))=k3_xboole_0(B_115, '#skF_1'('#skF_3', '#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_38, c_413])).
% 4.01/1.74  tff(c_8, plain, (![A_9]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.01/1.74  tff(c_53, plain, (![A_47, B_48, C_49]: (k9_subset_1(A_47, B_48, B_48)=B_48 | ~m1_subset_1(C_49, k1_zfmisc_1(A_47)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.01/1.74  tff(c_59, plain, (![A_9, B_48]: (k9_subset_1(A_9, B_48, B_48)=B_48)), inference(resolution, [status(thm)], [c_8, c_53])).
% 4.01/1.74  tff(c_423, plain, (k3_xboole_0('#skF_1'('#skF_3', '#skF_4'), '#skF_1'('#skF_3', '#skF_4'))='#skF_1'('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_416, c_59])).
% 4.01/1.74  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k3_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.01/1.74  tff(c_439, plain, (r1_tarski('#skF_1'('#skF_3', '#skF_4'), '#skF_1'('#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_423, c_2])).
% 4.01/1.74  tff(c_184, plain, (![A_73, B_74]: ('#skF_1'(A_73, B_74)!=B_74 | v3_tex_2(B_74, A_73) | ~v2_tex_2(B_74, A_73) | ~m1_subset_1(B_74, k1_zfmisc_1(u1_struct_0(A_73))) | ~l1_pre_topc(A_73))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.01/1.74  tff(c_187, plain, ('#skF_1'('#skF_3', '#skF_4')!='#skF_4' | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_44, c_184])).
% 4.01/1.74  tff(c_194, plain, ('#skF_1'('#skF_3', '#skF_4')!='#skF_4' | v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_40, c_187])).
% 4.01/1.74  tff(c_195, plain, ('#skF_1'('#skF_3', '#skF_4')!='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_38, c_194])).
% 4.01/1.74  tff(c_24, plain, (![A_23, B_29]: (m1_subset_1('#skF_1'(A_23, B_29), k1_zfmisc_1(u1_struct_0(A_23))) | v3_tex_2(B_29, A_23) | ~v2_tex_2(B_29, A_23) | ~m1_subset_1(B_29, k1_zfmisc_1(u1_struct_0(A_23))) | ~l1_pre_topc(A_23))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.01/1.74  tff(c_50, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.01/1.74  tff(c_48, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.01/1.74  tff(c_42, plain, (v1_tops_1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.01/1.74  tff(c_149, plain, (![A_66, B_67]: (k2_pre_topc(A_66, B_67)=u1_struct_0(A_66) | ~v1_tops_1(B_67, A_66) | ~m1_subset_1(B_67, k1_zfmisc_1(u1_struct_0(A_66))) | ~l1_pre_topc(A_66))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.01/1.74  tff(c_152, plain, (k2_pre_topc('#skF_3', '#skF_4')=u1_struct_0('#skF_3') | ~v1_tops_1('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_44, c_149])).
% 4.01/1.74  tff(c_159, plain, (k2_pre_topc('#skF_3', '#skF_4')=u1_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_42, c_152])).
% 4.01/1.74  tff(c_492, plain, (![A_120, B_121, C_122]: (k9_subset_1(u1_struct_0(A_120), B_121, k2_pre_topc(A_120, C_122))=C_122 | ~r1_tarski(C_122, B_121) | ~m1_subset_1(C_122, k1_zfmisc_1(u1_struct_0(A_120))) | ~v2_tex_2(B_121, A_120) | ~m1_subset_1(B_121, k1_zfmisc_1(u1_struct_0(A_120))) | ~l1_pre_topc(A_120) | ~v2_pre_topc(A_120) | v2_struct_0(A_120))), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.01/1.74  tff(c_498, plain, (![B_121]: (k9_subset_1(u1_struct_0('#skF_3'), B_121, k2_pre_topc('#skF_3', '#skF_4'))='#skF_4' | ~r1_tarski('#skF_4', B_121) | ~v2_tex_2(B_121, '#skF_3') | ~m1_subset_1(B_121, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_44, c_492])).
% 4.01/1.74  tff(c_506, plain, (![B_121]: (k9_subset_1(u1_struct_0('#skF_3'), B_121, u1_struct_0('#skF_3'))='#skF_4' | ~r1_tarski('#skF_4', B_121) | ~v2_tex_2(B_121, '#skF_3') | ~m1_subset_1(B_121, k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_159, c_498])).
% 4.01/1.74  tff(c_509, plain, (![B_123]: (k9_subset_1(u1_struct_0('#skF_3'), B_123, u1_struct_0('#skF_3'))='#skF_4' | ~r1_tarski('#skF_4', B_123) | ~v2_tex_2(B_123, '#skF_3') | ~m1_subset_1(B_123, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_50, c_506])).
% 4.01/1.74  tff(c_517, plain, (![B_29]: (k9_subset_1(u1_struct_0('#skF_3'), '#skF_1'('#skF_3', B_29), u1_struct_0('#skF_3'))='#skF_4' | ~r1_tarski('#skF_4', '#skF_1'('#skF_3', B_29)) | ~v2_tex_2('#skF_1'('#skF_3', B_29), '#skF_3') | v3_tex_2(B_29, '#skF_3') | ~v2_tex_2(B_29, '#skF_3') | ~m1_subset_1(B_29, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_24, c_509])).
% 4.01/1.74  tff(c_531, plain, (![B_29]: (k9_subset_1(u1_struct_0('#skF_3'), '#skF_1'('#skF_3', B_29), u1_struct_0('#skF_3'))='#skF_4' | ~r1_tarski('#skF_4', '#skF_1'('#skF_3', B_29)) | ~v2_tex_2('#skF_1'('#skF_3', B_29), '#skF_3') | v3_tex_2(B_29, '#skF_3') | ~v2_tex_2(B_29, '#skF_3') | ~m1_subset_1(B_29, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_517])).
% 4.01/1.74  tff(c_270, plain, (![C_87, A_88, B_89]: (v1_tops_1(C_87, A_88) | ~r1_tarski(B_89, C_87) | ~v1_tops_1(B_89, A_88) | ~m1_subset_1(C_87, k1_zfmisc_1(u1_struct_0(A_88))) | ~m1_subset_1(B_89, k1_zfmisc_1(u1_struct_0(A_88))) | ~l1_pre_topc(A_88))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.01/1.74  tff(c_367, plain, (![A_101]: (v1_tops_1('#skF_1'('#skF_3', '#skF_4'), A_101) | ~v1_tops_1('#skF_4', A_101) | ~m1_subset_1('#skF_1'('#skF_3', '#skF_4'), k1_zfmisc_1(u1_struct_0(A_101))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(A_101))) | ~l1_pre_topc(A_101))), inference(resolution, [status(thm)], [c_222, c_270])).
% 4.01/1.74  tff(c_371, plain, (v1_tops_1('#skF_1'('#skF_3', '#skF_4'), '#skF_3') | ~v1_tops_1('#skF_4', '#skF_3') | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_24, c_367])).
% 4.01/1.74  tff(c_374, plain, (v1_tops_1('#skF_1'('#skF_3', '#skF_4'), '#skF_3') | v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_40, c_42, c_371])).
% 4.01/1.74  tff(c_375, plain, (v1_tops_1('#skF_1'('#skF_3', '#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_38, c_374])).
% 4.01/1.74  tff(c_16, plain, (![A_20, B_22]: (k2_pre_topc(A_20, B_22)=u1_struct_0(A_20) | ~v1_tops_1(B_22, A_20) | ~m1_subset_1(B_22, k1_zfmisc_1(u1_struct_0(A_20))) | ~l1_pre_topc(A_20))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.01/1.74  tff(c_387, plain, (![A_108, B_109]: (k2_pre_topc(A_108, '#skF_1'(A_108, B_109))=u1_struct_0(A_108) | ~v1_tops_1('#skF_1'(A_108, B_109), A_108) | v3_tex_2(B_109, A_108) | ~v2_tex_2(B_109, A_108) | ~m1_subset_1(B_109, k1_zfmisc_1(u1_struct_0(A_108))) | ~l1_pre_topc(A_108))), inference(resolution, [status(thm)], [c_238, c_16])).
% 4.01/1.74  tff(c_389, plain, (k2_pre_topc('#skF_3', '#skF_1'('#skF_3', '#skF_4'))=u1_struct_0('#skF_3') | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_375, c_387])).
% 4.01/1.74  tff(c_392, plain, (k2_pre_topc('#skF_3', '#skF_1'('#skF_3', '#skF_4'))=u1_struct_0('#skF_3') | v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_40, c_389])).
% 4.01/1.74  tff(c_393, plain, (k2_pre_topc('#skF_3', '#skF_1'('#skF_3', '#skF_4'))=u1_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_38, c_392])).
% 4.01/1.74  tff(c_921, plain, (![A_193, B_194, B_195]: (k9_subset_1(u1_struct_0(A_193), B_194, k2_pre_topc(A_193, '#skF_1'(A_193, B_195)))='#skF_1'(A_193, B_195) | ~r1_tarski('#skF_1'(A_193, B_195), B_194) | ~v2_tex_2(B_194, A_193) | ~m1_subset_1(B_194, k1_zfmisc_1(u1_struct_0(A_193))) | ~v2_pre_topc(A_193) | v2_struct_0(A_193) | v3_tex_2(B_195, A_193) | ~v2_tex_2(B_195, A_193) | ~m1_subset_1(B_195, k1_zfmisc_1(u1_struct_0(A_193))) | ~l1_pre_topc(A_193))), inference(resolution, [status(thm)], [c_24, c_492])).
% 4.01/1.74  tff(c_937, plain, (![B_194]: (k9_subset_1(u1_struct_0('#skF_3'), B_194, u1_struct_0('#skF_3'))='#skF_1'('#skF_3', '#skF_4') | ~r1_tarski('#skF_1'('#skF_3', '#skF_4'), B_194) | ~v2_tex_2(B_194, '#skF_3') | ~m1_subset_1(B_194, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_393, c_921])).
% 4.01/1.74  tff(c_947, plain, (![B_194]: (k9_subset_1(u1_struct_0('#skF_3'), B_194, u1_struct_0('#skF_3'))='#skF_1'('#skF_3', '#skF_4') | ~r1_tarski('#skF_1'('#skF_3', '#skF_4'), B_194) | ~v2_tex_2(B_194, '#skF_3') | ~m1_subset_1(B_194, k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3') | v3_tex_2('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_40, c_48, c_937])).
% 4.01/1.74  tff(c_949, plain, (![B_196]: (k9_subset_1(u1_struct_0('#skF_3'), B_196, u1_struct_0('#skF_3'))='#skF_1'('#skF_3', '#skF_4') | ~r1_tarski('#skF_1'('#skF_3', '#skF_4'), B_196) | ~v2_tex_2(B_196, '#skF_3') | ~m1_subset_1(B_196, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_38, c_50, c_947])).
% 4.01/1.74  tff(c_957, plain, (![B_29]: (k9_subset_1(u1_struct_0('#skF_3'), '#skF_1'('#skF_3', B_29), u1_struct_0('#skF_3'))='#skF_1'('#skF_3', '#skF_4') | ~r1_tarski('#skF_1'('#skF_3', '#skF_4'), '#skF_1'('#skF_3', B_29)) | ~v2_tex_2('#skF_1'('#skF_3', B_29), '#skF_3') | v3_tex_2(B_29, '#skF_3') | ~v2_tex_2(B_29, '#skF_3') | ~m1_subset_1(B_29, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_24, c_949])).
% 4.01/1.74  tff(c_995, plain, (![B_199]: (k9_subset_1(u1_struct_0('#skF_3'), '#skF_1'('#skF_3', B_199), u1_struct_0('#skF_3'))='#skF_1'('#skF_3', '#skF_4') | ~r1_tarski('#skF_1'('#skF_3', '#skF_4'), '#skF_1'('#skF_3', B_199)) | ~v2_tex_2('#skF_1'('#skF_3', B_199), '#skF_3') | v3_tex_2(B_199, '#skF_3') | ~v2_tex_2(B_199, '#skF_3') | ~m1_subset_1(B_199, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_957])).
% 4.01/1.74  tff(c_1007, plain, (![B_29]: ('#skF_1'('#skF_3', '#skF_4')='#skF_4' | ~r1_tarski('#skF_1'('#skF_3', '#skF_4'), '#skF_1'('#skF_3', B_29)) | ~v2_tex_2('#skF_1'('#skF_3', B_29), '#skF_3') | v3_tex_2(B_29, '#skF_3') | ~v2_tex_2(B_29, '#skF_3') | ~m1_subset_1(B_29, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~r1_tarski('#skF_4', '#skF_1'('#skF_3', B_29)) | ~v2_tex_2('#skF_1'('#skF_3', B_29), '#skF_3') | v3_tex_2(B_29, '#skF_3') | ~v2_tex_2(B_29, '#skF_3') | ~m1_subset_1(B_29, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(superposition, [status(thm), theory('equality')], [c_531, c_995])).
% 4.01/1.74  tff(c_1085, plain, (![B_212]: (~r1_tarski('#skF_1'('#skF_3', '#skF_4'), '#skF_1'('#skF_3', B_212)) | ~v2_tex_2('#skF_1'('#skF_3', B_212), '#skF_3') | v3_tex_2(B_212, '#skF_3') | ~v2_tex_2(B_212, '#skF_3') | ~m1_subset_1(B_212, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~r1_tarski('#skF_4', '#skF_1'('#skF_3', B_212)) | ~v2_tex_2('#skF_1'('#skF_3', B_212), '#skF_3') | v3_tex_2(B_212, '#skF_3') | ~v2_tex_2(B_212, '#skF_3') | ~m1_subset_1(B_212, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_195, c_1007])).
% 4.01/1.74  tff(c_1092, plain, (~r1_tarski('#skF_4', '#skF_1'('#skF_3', '#skF_4')) | ~v2_tex_2('#skF_1'('#skF_3', '#skF_4'), '#skF_3') | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_439, c_1085])).
% 4.01/1.74  tff(c_1099, plain, (v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_40, c_211, c_222, c_1092])).
% 4.01/1.74  tff(c_1101, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_1099])).
% 4.01/1.74  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.01/1.74  
% 4.01/1.74  Inference rules
% 4.01/1.74  ----------------------
% 4.01/1.74  #Ref     : 0
% 4.01/1.74  #Sup     : 233
% 4.01/1.74  #Fact    : 0
% 4.01/1.74  #Define  : 0
% 4.01/1.74  #Split   : 3
% 4.01/1.74  #Chain   : 0
% 4.01/1.74  #Close   : 0
% 4.01/1.74  
% 4.01/1.74  Ordering : KBO
% 4.01/1.74  
% 4.01/1.74  Simplification rules
% 4.01/1.74  ----------------------
% 4.01/1.74  #Subsume      : 18
% 4.01/1.74  #Demod        : 111
% 4.01/1.74  #Tautology    : 100
% 4.01/1.74  #SimpNegUnit  : 27
% 4.01/1.74  #BackRed      : 0
% 4.01/1.74  
% 4.01/1.74  #Partial instantiations: 0
% 4.01/1.74  #Strategies tried      : 1
% 4.01/1.74  
% 4.01/1.74  Timing (in seconds)
% 4.01/1.74  ----------------------
% 4.01/1.74  Preprocessing        : 0.34
% 4.01/1.74  Parsing              : 0.19
% 4.01/1.74  CNF conversion       : 0.02
% 4.01/1.74  Main loop            : 0.56
% 4.01/1.74  Inferencing          : 0.23
% 4.01/1.74  Reduction            : 0.16
% 4.01/1.74  Demodulation         : 0.11
% 4.01/1.74  BG Simplification    : 0.03
% 4.01/1.74  Subsumption          : 0.11
% 4.01/1.74  Abstraction          : 0.03
% 4.01/1.74  MUC search           : 0.00
% 4.01/1.74  Cooper               : 0.00
% 4.01/1.74  Total                : 0.95
% 4.01/1.74  Index Insertion      : 0.00
% 4.01/1.74  Index Deletion       : 0.00
% 4.01/1.74  Index Matching       : 0.00
% 4.01/1.74  BG Taut test         : 0.00
%------------------------------------------------------------------------------
