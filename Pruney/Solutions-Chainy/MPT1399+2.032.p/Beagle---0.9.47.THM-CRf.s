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
% DateTime   : Thu Dec  3 10:24:23 EST 2020

% Result     : Theorem 2.50s
% Output     : CNFRefutation 2.56s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 236 expanded)
%              Number of leaves         :   40 ( 100 expanded)
%              Depth                    :   11
%              Number of atoms          :  129 ( 659 expanded)
%              Number of equality atoms :   13 (  95 expanded)
%              Maximal formula depth    :   15 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k9_subset_1 > k5_setfam_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > u1_pre_topc > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_6 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(k5_setfam_1,type,(
    k5_setfam_1: ( $i * $i ) > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_128,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
               => ~ ( ! [D] :
                        ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                       => ( r2_hidden(D,C)
                        <=> ( v3_pre_topc(D,A)
                            & v4_pre_topc(D,A)
                            & r2_hidden(B,D) ) ) )
                    & C = k1_xboole_0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_connsp_2)).

tff(f_86,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_73,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_94,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_44,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_100,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v4_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_pre_topc)).

tff(f_69,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_pre_topc)).

tff(f_36,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_38,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_82,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_pre_topc(B,A)
          <=> r2_hidden(B,u1_pre_topc(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_pre_topc)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_34,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(c_70,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_58,plain,(
    ! [A_27] :
      ( l1_struct_0(A_27)
      | ~ l1_pre_topc(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_74,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_132,plain,(
    ! [A_50] :
      ( u1_struct_0(A_50) = k2_struct_0(A_50)
      | ~ l1_struct_0(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_138,plain,(
    ! [A_52] :
      ( u1_struct_0(A_52) = k2_struct_0(A_52)
      | ~ l1_pre_topc(A_52) ) ),
    inference(resolution,[status(thm)],[c_58,c_132])).

tff(c_142,plain,(
    u1_struct_0('#skF_4') = k2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_70,c_138])).

tff(c_60,plain,(
    ! [A_28] :
      ( ~ v1_xboole_0(u1_struct_0(A_28))
      | ~ l1_struct_0(A_28)
      | v2_struct_0(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_148,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_4'))
    | ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_142,c_60])).

tff(c_151,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_4'))
    | ~ l1_struct_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_148])).

tff(c_154,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_151])).

tff(c_157,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_154])).

tff(c_161,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_157])).

tff(c_162,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_151])).

tff(c_68,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_144,plain,(
    m1_subset_1('#skF_5',k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_68])).

tff(c_14,plain,(
    ! [A_7,B_8] :
      ( r2_hidden(A_7,B_8)
      | v1_xboole_0(B_8)
      | ~ m1_subset_1(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_72,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_62,plain,(
    ! [A_29] :
      ( v4_pre_topc(k2_struct_0(A_29),A_29)
      | ~ l1_pre_topc(A_29)
      | ~ v2_pre_topc(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_195,plain,(
    ! [A_59] :
      ( r2_hidden(u1_struct_0(A_59),u1_pre_topc(A_59))
      | ~ v2_pre_topc(A_59)
      | ~ l1_pre_topc(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_198,plain,
    ( r2_hidden(k2_struct_0('#skF_4'),u1_pre_topc('#skF_4'))
    | ~ v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_142,c_195])).

tff(c_200,plain,(
    r2_hidden(k2_struct_0('#skF_4'),u1_pre_topc('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_72,c_198])).

tff(c_10,plain,(
    ! [A_5] : k2_subset_1(A_5) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_12,plain,(
    ! [A_6] : m1_subset_1(k2_subset_1(A_6),k1_zfmisc_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_83,plain,(
    ! [A_6] : m1_subset_1(A_6,k1_zfmisc_1(A_6)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_12])).

tff(c_235,plain,(
    ! [B_66,A_67] :
      ( v3_pre_topc(B_66,A_67)
      | ~ r2_hidden(B_66,u1_pre_topc(A_67))
      | ~ m1_subset_1(B_66,k1_zfmisc_1(u1_struct_0(A_67)))
      | ~ l1_pre_topc(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_254,plain,(
    ! [A_69] :
      ( v3_pre_topc(u1_struct_0(A_69),A_69)
      | ~ r2_hidden(u1_struct_0(A_69),u1_pre_topc(A_69))
      | ~ l1_pre_topc(A_69) ) ),
    inference(resolution,[status(thm)],[c_83,c_235])).

tff(c_266,plain,
    ( v3_pre_topc(u1_struct_0('#skF_4'),'#skF_4')
    | ~ r2_hidden(k2_struct_0('#skF_4'),u1_pre_topc('#skF_4'))
    | ~ l1_pre_topc('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_142,c_254])).

tff(c_271,plain,(
    v3_pre_topc(k2_struct_0('#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_200,c_142,c_266])).

tff(c_64,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_4,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_85,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_64,c_4])).

tff(c_124,plain,(
    ! [A_47,B_48] : ~ r2_hidden(A_47,k2_zfmisc_1(A_47,B_48)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_130,plain,(
    ! [A_1] : ~ r2_hidden(A_1,'#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_124])).

tff(c_76,plain,(
    ! [D_41] :
      ( r2_hidden(D_41,'#skF_6')
      | ~ r2_hidden('#skF_5',D_41)
      | ~ v4_pre_topc(D_41,'#skF_4')
      | ~ v3_pre_topc(D_41,'#skF_4')
      | ~ m1_subset_1(D_41,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_246,plain,(
    ! [D_41] :
      ( r2_hidden(D_41,'#skF_6')
      | ~ r2_hidden('#skF_5',D_41)
      | ~ v4_pre_topc(D_41,'#skF_4')
      | ~ v3_pre_topc(D_41,'#skF_4')
      | ~ m1_subset_1(D_41,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_76])).

tff(c_248,plain,(
    ! [D_68] :
      ( ~ r2_hidden('#skF_5',D_68)
      | ~ v4_pre_topc(D_68,'#skF_4')
      | ~ v3_pre_topc(D_68,'#skF_4')
      | ~ m1_subset_1(D_68,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_130,c_246])).

tff(c_253,plain,
    ( ~ r2_hidden('#skF_5',k2_struct_0('#skF_4'))
    | ~ v4_pre_topc(k2_struct_0('#skF_4'),'#skF_4')
    | ~ v3_pre_topc(k2_struct_0('#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_83,c_248])).

tff(c_287,plain,
    ( ~ r2_hidden('#skF_5',k2_struct_0('#skF_4'))
    | ~ v4_pre_topc(k2_struct_0('#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_271,c_253])).

tff(c_288,plain,(
    ~ v4_pre_topc(k2_struct_0('#skF_4'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_287])).

tff(c_309,plain,
    ( ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_288])).

tff(c_313,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_309])).

tff(c_314,plain,(
    ~ r2_hidden('#skF_5',k2_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_287])).

tff(c_318,plain,
    ( v1_xboole_0(k2_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_5',k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_14,c_314])).

tff(c_321,plain,(
    v1_xboole_0(k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_318])).

tff(c_323,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_162,c_321])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.34  % Computer   : n011.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % DateTime   : Tue Dec  1 11:12:12 EST 2020
% 0.15/0.34  % CPUTime    : 
% 0.15/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.50/1.46  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.50/1.46  
% 2.50/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.50/1.46  %$ v4_pre_topc > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k9_subset_1 > k5_setfam_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > u1_pre_topc > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_6 > #skF_4 > #skF_3
% 2.50/1.46  
% 2.50/1.46  %Foreground sorts:
% 2.50/1.46  
% 2.50/1.46  
% 2.50/1.46  %Background operators:
% 2.50/1.46  
% 2.50/1.46  
% 2.50/1.46  %Foreground operators:
% 2.50/1.46  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.50/1.46  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 2.50/1.46  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.50/1.46  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.50/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.50/1.46  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.50/1.46  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.50/1.46  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.50/1.46  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.50/1.46  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.50/1.46  tff('#skF_5', type, '#skF_5': $i).
% 2.50/1.46  tff('#skF_6', type, '#skF_6': $i).
% 2.50/1.46  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.50/1.46  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.50/1.46  tff(k5_setfam_1, type, k5_setfam_1: ($i * $i) > $i).
% 2.50/1.46  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.50/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.50/1.46  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.50/1.46  tff('#skF_4', type, '#skF_4': $i).
% 2.50/1.46  tff('#skF_3', type, '#skF_3': $i > $i).
% 2.50/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.50/1.46  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.50/1.46  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.50/1.46  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.50/1.46  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.50/1.46  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.50/1.46  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 2.50/1.46  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.50/1.46  
% 2.56/1.48  tff(f_128, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => ~((![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(D, C) <=> ((v3_pre_topc(D, A) & v4_pre_topc(D, A)) & r2_hidden(B, D))))) & (C = k1_xboole_0)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_connsp_2)).
% 2.56/1.48  tff(f_86, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.56/1.48  tff(f_73, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 2.56/1.48  tff(f_94, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.56/1.48  tff(f_44, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 2.56/1.48  tff(f_100, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v4_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_pre_topc)).
% 2.56/1.48  tff(f_69, axiom, (![A]: (l1_pre_topc(A) => (v2_pre_topc(A) <=> ((r2_hidden(u1_struct_0(A), u1_pre_topc(A)) & (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (r1_tarski(B, u1_pre_topc(A)) => r2_hidden(k5_setfam_1(u1_struct_0(A), B), u1_pre_topc(A)))))) & (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r2_hidden(B, u1_pre_topc(A)) & r2_hidden(C, u1_pre_topc(A))) => r2_hidden(k9_subset_1(u1_struct_0(A), B, C), u1_pre_topc(A))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_pre_topc)).
% 2.56/1.48  tff(f_36, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 2.56/1.48  tff(f_38, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 2.56/1.48  tff(f_82, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> r2_hidden(B, u1_pre_topc(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_pre_topc)).
% 2.56/1.48  tff(f_31, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.56/1.48  tff(f_34, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 2.56/1.48  tff(c_70, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_128])).
% 2.56/1.48  tff(c_58, plain, (![A_27]: (l1_struct_0(A_27) | ~l1_pre_topc(A_27))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.56/1.48  tff(c_74, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_128])).
% 2.56/1.48  tff(c_132, plain, (![A_50]: (u1_struct_0(A_50)=k2_struct_0(A_50) | ~l1_struct_0(A_50))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.56/1.48  tff(c_138, plain, (![A_52]: (u1_struct_0(A_52)=k2_struct_0(A_52) | ~l1_pre_topc(A_52))), inference(resolution, [status(thm)], [c_58, c_132])).
% 2.56/1.48  tff(c_142, plain, (u1_struct_0('#skF_4')=k2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_70, c_138])).
% 2.56/1.48  tff(c_60, plain, (![A_28]: (~v1_xboole_0(u1_struct_0(A_28)) | ~l1_struct_0(A_28) | v2_struct_0(A_28))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.56/1.48  tff(c_148, plain, (~v1_xboole_0(k2_struct_0('#skF_4')) | ~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_142, c_60])).
% 2.56/1.48  tff(c_151, plain, (~v1_xboole_0(k2_struct_0('#skF_4')) | ~l1_struct_0('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_74, c_148])).
% 2.56/1.48  tff(c_154, plain, (~l1_struct_0('#skF_4')), inference(splitLeft, [status(thm)], [c_151])).
% 2.56/1.48  tff(c_157, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_58, c_154])).
% 2.56/1.48  tff(c_161, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_157])).
% 2.56/1.48  tff(c_162, plain, (~v1_xboole_0(k2_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_151])).
% 2.56/1.48  tff(c_68, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_128])).
% 2.56/1.48  tff(c_144, plain, (m1_subset_1('#skF_5', k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_142, c_68])).
% 2.56/1.48  tff(c_14, plain, (![A_7, B_8]: (r2_hidden(A_7, B_8) | v1_xboole_0(B_8) | ~m1_subset_1(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.56/1.48  tff(c_72, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_128])).
% 2.56/1.48  tff(c_62, plain, (![A_29]: (v4_pre_topc(k2_struct_0(A_29), A_29) | ~l1_pre_topc(A_29) | ~v2_pre_topc(A_29))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.56/1.48  tff(c_195, plain, (![A_59]: (r2_hidden(u1_struct_0(A_59), u1_pre_topc(A_59)) | ~v2_pre_topc(A_59) | ~l1_pre_topc(A_59))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.56/1.48  tff(c_198, plain, (r2_hidden(k2_struct_0('#skF_4'), u1_pre_topc('#skF_4')) | ~v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_142, c_195])).
% 2.56/1.48  tff(c_200, plain, (r2_hidden(k2_struct_0('#skF_4'), u1_pre_topc('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_72, c_198])).
% 2.56/1.48  tff(c_10, plain, (![A_5]: (k2_subset_1(A_5)=A_5)), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.56/1.48  tff(c_12, plain, (![A_6]: (m1_subset_1(k2_subset_1(A_6), k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.56/1.48  tff(c_83, plain, (![A_6]: (m1_subset_1(A_6, k1_zfmisc_1(A_6)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_12])).
% 2.56/1.48  tff(c_235, plain, (![B_66, A_67]: (v3_pre_topc(B_66, A_67) | ~r2_hidden(B_66, u1_pre_topc(A_67)) | ~m1_subset_1(B_66, k1_zfmisc_1(u1_struct_0(A_67))) | ~l1_pre_topc(A_67))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.56/1.48  tff(c_254, plain, (![A_69]: (v3_pre_topc(u1_struct_0(A_69), A_69) | ~r2_hidden(u1_struct_0(A_69), u1_pre_topc(A_69)) | ~l1_pre_topc(A_69))), inference(resolution, [status(thm)], [c_83, c_235])).
% 2.56/1.48  tff(c_266, plain, (v3_pre_topc(u1_struct_0('#skF_4'), '#skF_4') | ~r2_hidden(k2_struct_0('#skF_4'), u1_pre_topc('#skF_4')) | ~l1_pre_topc('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_142, c_254])).
% 2.56/1.48  tff(c_271, plain, (v3_pre_topc(k2_struct_0('#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_200, c_142, c_266])).
% 2.56/1.48  tff(c_64, plain, (k1_xboole_0='#skF_6'), inference(cnfTransformation, [status(thm)], [f_128])).
% 2.56/1.48  tff(c_4, plain, (![A_1]: (k2_zfmisc_1(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.56/1.48  tff(c_85, plain, (![A_1]: (k2_zfmisc_1(A_1, '#skF_6')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_64, c_4])).
% 2.56/1.48  tff(c_124, plain, (![A_47, B_48]: (~r2_hidden(A_47, k2_zfmisc_1(A_47, B_48)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.56/1.48  tff(c_130, plain, (![A_1]: (~r2_hidden(A_1, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_85, c_124])).
% 2.56/1.48  tff(c_76, plain, (![D_41]: (r2_hidden(D_41, '#skF_6') | ~r2_hidden('#skF_5', D_41) | ~v4_pre_topc(D_41, '#skF_4') | ~v3_pre_topc(D_41, '#skF_4') | ~m1_subset_1(D_41, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_128])).
% 2.56/1.48  tff(c_246, plain, (![D_41]: (r2_hidden(D_41, '#skF_6') | ~r2_hidden('#skF_5', D_41) | ~v4_pre_topc(D_41, '#skF_4') | ~v3_pre_topc(D_41, '#skF_4') | ~m1_subset_1(D_41, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_142, c_76])).
% 2.56/1.48  tff(c_248, plain, (![D_68]: (~r2_hidden('#skF_5', D_68) | ~v4_pre_topc(D_68, '#skF_4') | ~v3_pre_topc(D_68, '#skF_4') | ~m1_subset_1(D_68, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_130, c_246])).
% 2.56/1.48  tff(c_253, plain, (~r2_hidden('#skF_5', k2_struct_0('#skF_4')) | ~v4_pre_topc(k2_struct_0('#skF_4'), '#skF_4') | ~v3_pre_topc(k2_struct_0('#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_83, c_248])).
% 2.56/1.48  tff(c_287, plain, (~r2_hidden('#skF_5', k2_struct_0('#skF_4')) | ~v4_pre_topc(k2_struct_0('#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_271, c_253])).
% 2.56/1.48  tff(c_288, plain, (~v4_pre_topc(k2_struct_0('#skF_4'), '#skF_4')), inference(splitLeft, [status(thm)], [c_287])).
% 2.56/1.48  tff(c_309, plain, (~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_62, c_288])).
% 2.56/1.48  tff(c_313, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_309])).
% 2.56/1.48  tff(c_314, plain, (~r2_hidden('#skF_5', k2_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_287])).
% 2.56/1.48  tff(c_318, plain, (v1_xboole_0(k2_struct_0('#skF_4')) | ~m1_subset_1('#skF_5', k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_14, c_314])).
% 2.56/1.48  tff(c_321, plain, (v1_xboole_0(k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_144, c_318])).
% 2.56/1.48  tff(c_323, plain, $false, inference(negUnitSimplification, [status(thm)], [c_162, c_321])).
% 2.56/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.56/1.48  
% 2.56/1.48  Inference rules
% 2.56/1.48  ----------------------
% 2.56/1.48  #Ref     : 0
% 2.56/1.48  #Sup     : 45
% 2.56/1.48  #Fact    : 0
% 2.56/1.48  #Define  : 0
% 2.56/1.48  #Split   : 3
% 2.56/1.48  #Chain   : 0
% 2.56/1.48  #Close   : 0
% 2.56/1.48  
% 2.56/1.48  Ordering : KBO
% 2.56/1.48  
% 2.56/1.48  Simplification rules
% 2.56/1.48  ----------------------
% 2.56/1.48  #Subsume      : 6
% 2.56/1.48  #Demod        : 41
% 2.56/1.48  #Tautology    : 22
% 2.56/1.48  #SimpNegUnit  : 3
% 2.56/1.48  #BackRed      : 2
% 2.56/1.48  
% 2.56/1.48  #Partial instantiations: 0
% 2.56/1.48  #Strategies tried      : 1
% 2.56/1.48  
% 2.56/1.48  Timing (in seconds)
% 2.56/1.48  ----------------------
% 2.56/1.48  Preprocessing        : 0.41
% 2.56/1.48  Parsing              : 0.22
% 2.56/1.48  CNF conversion       : 0.03
% 2.56/1.48  Main loop            : 0.21
% 2.56/1.48  Inferencing          : 0.06
% 2.56/1.48  Reduction            : 0.07
% 2.56/1.48  Demodulation         : 0.05
% 2.56/1.48  BG Simplification    : 0.02
% 2.56/1.48  Subsumption          : 0.04
% 2.56/1.49  Abstraction          : 0.01
% 2.56/1.49  MUC search           : 0.00
% 2.56/1.49  Cooper               : 0.00
% 2.56/1.49  Total                : 0.65
% 2.56/1.49  Index Insertion      : 0.00
% 2.56/1.49  Index Deletion       : 0.00
% 2.56/1.49  Index Matching       : 0.00
% 2.56/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
