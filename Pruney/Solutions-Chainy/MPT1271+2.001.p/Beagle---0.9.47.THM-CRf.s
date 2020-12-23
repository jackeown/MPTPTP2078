%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:58 EST 2020

% Result     : Theorem 2.32s
% Output     : CNFRefutation 2.32s
% Verified   : 
% Statistics : Number of formulae       :   50 (  75 expanded)
%              Number of leaves         :   23 (  39 expanded)
%              Depth                    :    8
%              Number of atoms          :  142 ( 258 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_tops_1 > v2_tops_1 > m1_subset_1 > v2_pre_topc > l1_pre_topc > k4_subset_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v2_tops_1,type,(
    v2_tops_1: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v3_tops_1,type,(
    v3_tops_1: ( $i * $i ) > $o )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

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

tff(f_101,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( ( v3_tops_1(B,A)
                    & v3_tops_1(C,A) )
                 => v3_tops_1(k4_subset_1(u1_struct_0(A),B,C),A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_tops_1)).

tff(f_58,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_tops_1(B,A)
          <=> v2_tops_1(k2_pre_topc(A,B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tops_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v4_pre_topc(k2_pre_topc(A,B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_tops_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => m1_subset_1(k4_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_subset_1)).

tff(f_49,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => k2_pre_topc(A,k4_subset_1(u1_struct_0(A),B,C)) = k4_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k2_pre_topc(A,C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_pre_topc)).

tff(f_84,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( v2_tops_1(B,A)
                  & v2_tops_1(C,A)
                  & v4_pre_topc(C,A) )
               => v2_tops_1(k4_subset_1(u1_struct_0(A),B,C),A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_tops_1)).

tff(c_26,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_24,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_22,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_28,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_20,plain,(
    v3_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_44,plain,(
    ! [A_33,B_34] :
      ( v2_tops_1(k2_pre_topc(A_33,B_34),A_33)
      | ~ v3_tops_1(B_34,A_33)
      | ~ m1_subset_1(B_34,k1_zfmisc_1(u1_struct_0(A_33)))
      | ~ l1_pre_topc(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_48,plain,
    ( v2_tops_1(k2_pre_topc('#skF_1','#skF_2'),'#skF_1')
    | ~ v3_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_44])).

tff(c_54,plain,(
    v2_tops_1(k2_pre_topc('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_20,c_48])).

tff(c_18,plain,(
    v3_tops_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_50,plain,
    ( v2_tops_1(k2_pre_topc('#skF_1','#skF_3'),'#skF_1')
    | ~ v3_tops_1('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_44])).

tff(c_57,plain,(
    v2_tops_1(k2_pre_topc('#skF_1','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_18,c_50])).

tff(c_29,plain,(
    ! [A_29,B_30] :
      ( v4_pre_topc(k2_pre_topc(A_29,B_30),A_29)
      | ~ m1_subset_1(B_30,k1_zfmisc_1(u1_struct_0(A_29)))
      | ~ l1_pre_topc(A_29)
      | ~ v2_pre_topc(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_33,plain,
    ( v4_pre_topc(k2_pre_topc('#skF_1','#skF_3'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_29])).

tff(c_39,plain,(
    v4_pre_topc(k2_pre_topc('#skF_1','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_33])).

tff(c_4,plain,(
    ! [A_4,B_5] :
      ( m1_subset_1(k2_pre_topc(A_4,B_5),k1_zfmisc_1(u1_struct_0(A_4)))
      | ~ m1_subset_1(B_5,k1_zfmisc_1(u1_struct_0(A_4)))
      | ~ l1_pre_topc(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3] :
      ( m1_subset_1(k4_subset_1(A_1,B_2,C_3),k1_zfmisc_1(A_1))
      | ~ m1_subset_1(C_3,k1_zfmisc_1(A_1))
      | ~ m1_subset_1(B_2,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_6,plain,(
    ! [A_6,B_10,C_12] :
      ( k4_subset_1(u1_struct_0(A_6),k2_pre_topc(A_6,B_10),k2_pre_topc(A_6,C_12)) = k2_pre_topc(A_6,k4_subset_1(u1_struct_0(A_6),B_10,C_12))
      | ~ m1_subset_1(C_12,k1_zfmisc_1(u1_struct_0(A_6)))
      | ~ m1_subset_1(B_10,k1_zfmisc_1(u1_struct_0(A_6)))
      | ~ l1_pre_topc(A_6)
      | ~ v2_pre_topc(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_106,plain,(
    ! [A_53,B_54,C_55] :
      ( v2_tops_1(k4_subset_1(u1_struct_0(A_53),B_54,C_55),A_53)
      | ~ v4_pre_topc(C_55,A_53)
      | ~ v2_tops_1(C_55,A_53)
      | ~ v2_tops_1(B_54,A_53)
      | ~ m1_subset_1(C_55,k1_zfmisc_1(u1_struct_0(A_53)))
      | ~ m1_subset_1(B_54,k1_zfmisc_1(u1_struct_0(A_53)))
      | ~ l1_pre_topc(A_53)
      | ~ v2_pre_topc(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_124,plain,(
    ! [A_62,B_63,C_64] :
      ( v2_tops_1(k2_pre_topc(A_62,k4_subset_1(u1_struct_0(A_62),B_63,C_64)),A_62)
      | ~ v4_pre_topc(k2_pre_topc(A_62,C_64),A_62)
      | ~ v2_tops_1(k2_pre_topc(A_62,C_64),A_62)
      | ~ v2_tops_1(k2_pre_topc(A_62,B_63),A_62)
      | ~ m1_subset_1(k2_pre_topc(A_62,C_64),k1_zfmisc_1(u1_struct_0(A_62)))
      | ~ m1_subset_1(k2_pre_topc(A_62,B_63),k1_zfmisc_1(u1_struct_0(A_62)))
      | ~ l1_pre_topc(A_62)
      | ~ v2_pre_topc(A_62)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(u1_struct_0(A_62)))
      | ~ m1_subset_1(B_63,k1_zfmisc_1(u1_struct_0(A_62)))
      | ~ l1_pre_topc(A_62)
      | ~ v2_pre_topc(A_62) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_106])).

tff(c_8,plain,(
    ! [B_15,A_13] :
      ( v3_tops_1(B_15,A_13)
      | ~ v2_tops_1(k2_pre_topc(A_13,B_15),A_13)
      | ~ m1_subset_1(B_15,k1_zfmisc_1(u1_struct_0(A_13)))
      | ~ l1_pre_topc(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_142,plain,(
    ! [A_71,B_72,C_73] :
      ( v3_tops_1(k4_subset_1(u1_struct_0(A_71),B_72,C_73),A_71)
      | ~ m1_subset_1(k4_subset_1(u1_struct_0(A_71),B_72,C_73),k1_zfmisc_1(u1_struct_0(A_71)))
      | ~ v4_pre_topc(k2_pre_topc(A_71,C_73),A_71)
      | ~ v2_tops_1(k2_pre_topc(A_71,C_73),A_71)
      | ~ v2_tops_1(k2_pre_topc(A_71,B_72),A_71)
      | ~ m1_subset_1(k2_pre_topc(A_71,C_73),k1_zfmisc_1(u1_struct_0(A_71)))
      | ~ m1_subset_1(k2_pre_topc(A_71,B_72),k1_zfmisc_1(u1_struct_0(A_71)))
      | ~ m1_subset_1(C_73,k1_zfmisc_1(u1_struct_0(A_71)))
      | ~ m1_subset_1(B_72,k1_zfmisc_1(u1_struct_0(A_71)))
      | ~ l1_pre_topc(A_71)
      | ~ v2_pre_topc(A_71) ) ),
    inference(resolution,[status(thm)],[c_124,c_8])).

tff(c_151,plain,(
    ! [A_74,B_75,C_76] :
      ( v3_tops_1(k4_subset_1(u1_struct_0(A_74),B_75,C_76),A_74)
      | ~ v4_pre_topc(k2_pre_topc(A_74,C_76),A_74)
      | ~ v2_tops_1(k2_pre_topc(A_74,C_76),A_74)
      | ~ v2_tops_1(k2_pre_topc(A_74,B_75),A_74)
      | ~ m1_subset_1(k2_pre_topc(A_74,C_76),k1_zfmisc_1(u1_struct_0(A_74)))
      | ~ m1_subset_1(k2_pre_topc(A_74,B_75),k1_zfmisc_1(u1_struct_0(A_74)))
      | ~ l1_pre_topc(A_74)
      | ~ v2_pre_topc(A_74)
      | ~ m1_subset_1(C_76,k1_zfmisc_1(u1_struct_0(A_74)))
      | ~ m1_subset_1(B_75,k1_zfmisc_1(u1_struct_0(A_74))) ) ),
    inference(resolution,[status(thm)],[c_2,c_142])).

tff(c_158,plain,(
    ! [A_77,B_78,B_79] :
      ( v3_tops_1(k4_subset_1(u1_struct_0(A_77),B_78,B_79),A_77)
      | ~ v4_pre_topc(k2_pre_topc(A_77,B_79),A_77)
      | ~ v2_tops_1(k2_pre_topc(A_77,B_79),A_77)
      | ~ v2_tops_1(k2_pre_topc(A_77,B_78),A_77)
      | ~ m1_subset_1(k2_pre_topc(A_77,B_78),k1_zfmisc_1(u1_struct_0(A_77)))
      | ~ v2_pre_topc(A_77)
      | ~ m1_subset_1(B_78,k1_zfmisc_1(u1_struct_0(A_77)))
      | ~ m1_subset_1(B_79,k1_zfmisc_1(u1_struct_0(A_77)))
      | ~ l1_pre_topc(A_77) ) ),
    inference(resolution,[status(thm)],[c_4,c_151])).

tff(c_165,plain,(
    ! [A_80,B_81,B_82] :
      ( v3_tops_1(k4_subset_1(u1_struct_0(A_80),B_81,B_82),A_80)
      | ~ v4_pre_topc(k2_pre_topc(A_80,B_82),A_80)
      | ~ v2_tops_1(k2_pre_topc(A_80,B_82),A_80)
      | ~ v2_tops_1(k2_pre_topc(A_80,B_81),A_80)
      | ~ v2_pre_topc(A_80)
      | ~ m1_subset_1(B_82,k1_zfmisc_1(u1_struct_0(A_80)))
      | ~ m1_subset_1(B_81,k1_zfmisc_1(u1_struct_0(A_80)))
      | ~ l1_pre_topc(A_80) ) ),
    inference(resolution,[status(thm)],[c_4,c_158])).

tff(c_16,plain,(
    ~ v3_tops_1(k4_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_172,plain,
    ( ~ v4_pre_topc(k2_pre_topc('#skF_1','#skF_3'),'#skF_1')
    | ~ v2_tops_1(k2_pre_topc('#skF_1','#skF_3'),'#skF_1')
    | ~ v2_tops_1(k2_pre_topc('#skF_1','#skF_2'),'#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_165,c_16])).

tff(c_180,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_22,c_28,c_54,c_57,c_39,c_172])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:00:34 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.32/1.28  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.32/1.28  
% 2.32/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.32/1.29  %$ v4_pre_topc > v3_tops_1 > v2_tops_1 > m1_subset_1 > v2_pre_topc > l1_pre_topc > k4_subset_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 2.32/1.29  
% 2.32/1.29  %Foreground sorts:
% 2.32/1.29  
% 2.32/1.29  
% 2.32/1.29  %Background operators:
% 2.32/1.29  
% 2.32/1.29  
% 2.32/1.29  %Foreground operators:
% 2.32/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.32/1.29  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 2.32/1.29  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.32/1.29  tff(v3_tops_1, type, v3_tops_1: ($i * $i) > $o).
% 2.32/1.29  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 2.32/1.29  tff('#skF_2', type, '#skF_2': $i).
% 2.32/1.29  tff('#skF_3', type, '#skF_3': $i).
% 2.32/1.29  tff('#skF_1', type, '#skF_1': $i).
% 2.32/1.29  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.32/1.29  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.32/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.32/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.32/1.29  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.32/1.29  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.32/1.29  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.32/1.29  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.32/1.29  
% 2.32/1.30  tff(f_101, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v3_tops_1(B, A) & v3_tops_1(C, A)) => v3_tops_1(k4_subset_1(u1_struct_0(A), B, C), A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_tops_1)).
% 2.32/1.30  tff(f_58, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tops_1(B, A) <=> v2_tops_1(k2_pre_topc(A, B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tops_1)).
% 2.32/1.30  tff(f_66, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v4_pre_topc(k2_pre_topc(A, B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_tops_1)).
% 2.32/1.30  tff(f_37, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 2.32/1.30  tff(f_31, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => m1_subset_1(k4_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_subset_1)).
% 2.32/1.30  tff(f_49, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, k4_subset_1(u1_struct_0(A), B, C)) = k4_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k2_pre_topc(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_pre_topc)).
% 2.32/1.30  tff(f_84, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (((v2_tops_1(B, A) & v2_tops_1(C, A)) & v4_pre_topc(C, A)) => v2_tops_1(k4_subset_1(u1_struct_0(A), B, C), A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t85_tops_1)).
% 2.32/1.30  tff(c_26, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.32/1.30  tff(c_24, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.32/1.30  tff(c_22, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.32/1.30  tff(c_28, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.32/1.30  tff(c_20, plain, (v3_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.32/1.30  tff(c_44, plain, (![A_33, B_34]: (v2_tops_1(k2_pre_topc(A_33, B_34), A_33) | ~v3_tops_1(B_34, A_33) | ~m1_subset_1(B_34, k1_zfmisc_1(u1_struct_0(A_33))) | ~l1_pre_topc(A_33))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.32/1.30  tff(c_48, plain, (v2_tops_1(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1') | ~v3_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_24, c_44])).
% 2.32/1.30  tff(c_54, plain, (v2_tops_1(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_20, c_48])).
% 2.32/1.30  tff(c_18, plain, (v3_tops_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.32/1.30  tff(c_50, plain, (v2_tops_1(k2_pre_topc('#skF_1', '#skF_3'), '#skF_1') | ~v3_tops_1('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_22, c_44])).
% 2.32/1.30  tff(c_57, plain, (v2_tops_1(k2_pre_topc('#skF_1', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_18, c_50])).
% 2.32/1.30  tff(c_29, plain, (![A_29, B_30]: (v4_pre_topc(k2_pre_topc(A_29, B_30), A_29) | ~m1_subset_1(B_30, k1_zfmisc_1(u1_struct_0(A_29))) | ~l1_pre_topc(A_29) | ~v2_pre_topc(A_29))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.32/1.30  tff(c_33, plain, (v4_pre_topc(k2_pre_topc('#skF_1', '#skF_3'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_22, c_29])).
% 2.32/1.30  tff(c_39, plain, (v4_pre_topc(k2_pre_topc('#skF_1', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_33])).
% 2.32/1.30  tff(c_4, plain, (![A_4, B_5]: (m1_subset_1(k2_pre_topc(A_4, B_5), k1_zfmisc_1(u1_struct_0(A_4))) | ~m1_subset_1(B_5, k1_zfmisc_1(u1_struct_0(A_4))) | ~l1_pre_topc(A_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.32/1.30  tff(c_2, plain, (![A_1, B_2, C_3]: (m1_subset_1(k4_subset_1(A_1, B_2, C_3), k1_zfmisc_1(A_1)) | ~m1_subset_1(C_3, k1_zfmisc_1(A_1)) | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.32/1.30  tff(c_6, plain, (![A_6, B_10, C_12]: (k4_subset_1(u1_struct_0(A_6), k2_pre_topc(A_6, B_10), k2_pre_topc(A_6, C_12))=k2_pre_topc(A_6, k4_subset_1(u1_struct_0(A_6), B_10, C_12)) | ~m1_subset_1(C_12, k1_zfmisc_1(u1_struct_0(A_6))) | ~m1_subset_1(B_10, k1_zfmisc_1(u1_struct_0(A_6))) | ~l1_pre_topc(A_6) | ~v2_pre_topc(A_6))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.32/1.30  tff(c_106, plain, (![A_53, B_54, C_55]: (v2_tops_1(k4_subset_1(u1_struct_0(A_53), B_54, C_55), A_53) | ~v4_pre_topc(C_55, A_53) | ~v2_tops_1(C_55, A_53) | ~v2_tops_1(B_54, A_53) | ~m1_subset_1(C_55, k1_zfmisc_1(u1_struct_0(A_53))) | ~m1_subset_1(B_54, k1_zfmisc_1(u1_struct_0(A_53))) | ~l1_pre_topc(A_53) | ~v2_pre_topc(A_53))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.32/1.30  tff(c_124, plain, (![A_62, B_63, C_64]: (v2_tops_1(k2_pre_topc(A_62, k4_subset_1(u1_struct_0(A_62), B_63, C_64)), A_62) | ~v4_pre_topc(k2_pre_topc(A_62, C_64), A_62) | ~v2_tops_1(k2_pre_topc(A_62, C_64), A_62) | ~v2_tops_1(k2_pre_topc(A_62, B_63), A_62) | ~m1_subset_1(k2_pre_topc(A_62, C_64), k1_zfmisc_1(u1_struct_0(A_62))) | ~m1_subset_1(k2_pre_topc(A_62, B_63), k1_zfmisc_1(u1_struct_0(A_62))) | ~l1_pre_topc(A_62) | ~v2_pre_topc(A_62) | ~m1_subset_1(C_64, k1_zfmisc_1(u1_struct_0(A_62))) | ~m1_subset_1(B_63, k1_zfmisc_1(u1_struct_0(A_62))) | ~l1_pre_topc(A_62) | ~v2_pre_topc(A_62))), inference(superposition, [status(thm), theory('equality')], [c_6, c_106])).
% 2.32/1.30  tff(c_8, plain, (![B_15, A_13]: (v3_tops_1(B_15, A_13) | ~v2_tops_1(k2_pre_topc(A_13, B_15), A_13) | ~m1_subset_1(B_15, k1_zfmisc_1(u1_struct_0(A_13))) | ~l1_pre_topc(A_13))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.32/1.30  tff(c_142, plain, (![A_71, B_72, C_73]: (v3_tops_1(k4_subset_1(u1_struct_0(A_71), B_72, C_73), A_71) | ~m1_subset_1(k4_subset_1(u1_struct_0(A_71), B_72, C_73), k1_zfmisc_1(u1_struct_0(A_71))) | ~v4_pre_topc(k2_pre_topc(A_71, C_73), A_71) | ~v2_tops_1(k2_pre_topc(A_71, C_73), A_71) | ~v2_tops_1(k2_pre_topc(A_71, B_72), A_71) | ~m1_subset_1(k2_pre_topc(A_71, C_73), k1_zfmisc_1(u1_struct_0(A_71))) | ~m1_subset_1(k2_pre_topc(A_71, B_72), k1_zfmisc_1(u1_struct_0(A_71))) | ~m1_subset_1(C_73, k1_zfmisc_1(u1_struct_0(A_71))) | ~m1_subset_1(B_72, k1_zfmisc_1(u1_struct_0(A_71))) | ~l1_pre_topc(A_71) | ~v2_pre_topc(A_71))), inference(resolution, [status(thm)], [c_124, c_8])).
% 2.32/1.30  tff(c_151, plain, (![A_74, B_75, C_76]: (v3_tops_1(k4_subset_1(u1_struct_0(A_74), B_75, C_76), A_74) | ~v4_pre_topc(k2_pre_topc(A_74, C_76), A_74) | ~v2_tops_1(k2_pre_topc(A_74, C_76), A_74) | ~v2_tops_1(k2_pre_topc(A_74, B_75), A_74) | ~m1_subset_1(k2_pre_topc(A_74, C_76), k1_zfmisc_1(u1_struct_0(A_74))) | ~m1_subset_1(k2_pre_topc(A_74, B_75), k1_zfmisc_1(u1_struct_0(A_74))) | ~l1_pre_topc(A_74) | ~v2_pre_topc(A_74) | ~m1_subset_1(C_76, k1_zfmisc_1(u1_struct_0(A_74))) | ~m1_subset_1(B_75, k1_zfmisc_1(u1_struct_0(A_74))))), inference(resolution, [status(thm)], [c_2, c_142])).
% 2.32/1.30  tff(c_158, plain, (![A_77, B_78, B_79]: (v3_tops_1(k4_subset_1(u1_struct_0(A_77), B_78, B_79), A_77) | ~v4_pre_topc(k2_pre_topc(A_77, B_79), A_77) | ~v2_tops_1(k2_pre_topc(A_77, B_79), A_77) | ~v2_tops_1(k2_pre_topc(A_77, B_78), A_77) | ~m1_subset_1(k2_pre_topc(A_77, B_78), k1_zfmisc_1(u1_struct_0(A_77))) | ~v2_pre_topc(A_77) | ~m1_subset_1(B_78, k1_zfmisc_1(u1_struct_0(A_77))) | ~m1_subset_1(B_79, k1_zfmisc_1(u1_struct_0(A_77))) | ~l1_pre_topc(A_77))), inference(resolution, [status(thm)], [c_4, c_151])).
% 2.32/1.30  tff(c_165, plain, (![A_80, B_81, B_82]: (v3_tops_1(k4_subset_1(u1_struct_0(A_80), B_81, B_82), A_80) | ~v4_pre_topc(k2_pre_topc(A_80, B_82), A_80) | ~v2_tops_1(k2_pre_topc(A_80, B_82), A_80) | ~v2_tops_1(k2_pre_topc(A_80, B_81), A_80) | ~v2_pre_topc(A_80) | ~m1_subset_1(B_82, k1_zfmisc_1(u1_struct_0(A_80))) | ~m1_subset_1(B_81, k1_zfmisc_1(u1_struct_0(A_80))) | ~l1_pre_topc(A_80))), inference(resolution, [status(thm)], [c_4, c_158])).
% 2.32/1.30  tff(c_16, plain, (~v3_tops_1(k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.32/1.30  tff(c_172, plain, (~v4_pre_topc(k2_pre_topc('#skF_1', '#skF_3'), '#skF_1') | ~v2_tops_1(k2_pre_topc('#skF_1', '#skF_3'), '#skF_1') | ~v2_tops_1(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1') | ~v2_pre_topc('#skF_1') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_165, c_16])).
% 2.32/1.30  tff(c_180, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_22, c_28, c_54, c_57, c_39, c_172])).
% 2.32/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.32/1.30  
% 2.32/1.30  Inference rules
% 2.32/1.30  ----------------------
% 2.32/1.30  #Ref     : 0
% 2.32/1.30  #Sup     : 36
% 2.32/1.30  #Fact    : 0
% 2.32/1.30  #Define  : 0
% 2.32/1.30  #Split   : 0
% 2.32/1.30  #Chain   : 0
% 2.32/1.30  #Close   : 0
% 2.32/1.30  
% 2.32/1.30  Ordering : KBO
% 2.32/1.30  
% 2.32/1.30  Simplification rules
% 2.32/1.30  ----------------------
% 2.32/1.30  #Subsume      : 5
% 2.32/1.30  #Demod        : 21
% 2.32/1.30  #Tautology    : 7
% 2.32/1.30  #SimpNegUnit  : 0
% 2.32/1.30  #BackRed      : 0
% 2.32/1.30  
% 2.32/1.30  #Partial instantiations: 0
% 2.32/1.30  #Strategies tried      : 1
% 2.32/1.30  
% 2.32/1.30  Timing (in seconds)
% 2.32/1.30  ----------------------
% 2.32/1.31  Preprocessing        : 0.29
% 2.32/1.31  Parsing              : 0.16
% 2.32/1.31  CNF conversion       : 0.02
% 2.32/1.31  Main loop            : 0.24
% 2.32/1.31  Inferencing          : 0.10
% 2.32/1.31  Reduction            : 0.06
% 2.32/1.31  Demodulation         : 0.05
% 2.32/1.31  BG Simplification    : 0.01
% 2.32/1.31  Subsumption          : 0.05
% 2.32/1.31  Abstraction          : 0.01
% 2.32/1.31  MUC search           : 0.00
% 2.32/1.31  Cooper               : 0.00
% 2.32/1.31  Total                : 0.57
% 2.32/1.31  Index Insertion      : 0.00
% 2.32/1.31  Index Deletion       : 0.00
% 2.32/1.31  Index Matching       : 0.00
% 2.32/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
