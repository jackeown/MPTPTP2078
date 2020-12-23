%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:23 EST 2020

% Result     : Theorem 2.56s
% Output     : CNFRefutation 2.56s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 253 expanded)
%              Number of leaves         :   39 ( 104 expanded)
%              Depth                    :   15
%              Number of atoms          :  135 ( 686 expanded)
%              Number of equality atoms :    8 (  92 expanded)
%              Maximal formula depth    :   15 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k9_subset_1 > k5_setfam_1 > #nlpp > u1_struct_0 > u1_pre_topc > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_6 > #skF_4 > #skF_3

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

tff(f_126,negated_conjecture,(
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

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_84,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_71,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_90,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v4_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_pre_topc)).

tff(f_29,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_31,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_67,axiom,(
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

tff(f_80,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_pre_topc(B,A)
          <=> r2_hidden(B,u1_pre_topc(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_pre_topc)).

tff(f_98,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(k2_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_struct_0)).

tff(f_42,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_60,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_80,plain,(
    ! [A_1] : r1_tarski('#skF_6',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_2])).

tff(c_66,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_54,plain,(
    ! [A_26] :
      ( l1_struct_0(A_26)
      | ~ l1_pre_topc(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_70,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_97,plain,(
    ! [A_45] :
      ( u1_struct_0(A_45) = k2_struct_0(A_45)
      | ~ l1_struct_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_103,plain,(
    ! [A_48] :
      ( u1_struct_0(A_48) = k2_struct_0(A_48)
      | ~ l1_pre_topc(A_48) ) ),
    inference(resolution,[status(thm)],[c_54,c_97])).

tff(c_107,plain,(
    u1_struct_0('#skF_4') = k2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_103])).

tff(c_64,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_109,plain,(
    m1_subset_1('#skF_5',k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_64])).

tff(c_8,plain,(
    ! [A_4,B_5] :
      ( r2_hidden(A_4,B_5)
      | v1_xboole_0(B_5)
      | ~ m1_subset_1(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_68,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_56,plain,(
    ! [A_27] :
      ( v4_pre_topc(k2_struct_0(A_27),A_27)
      | ~ l1_pre_topc(A_27)
      | ~ v2_pre_topc(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_4,plain,(
    ! [A_2] : k2_subset_1(A_2) = A_2 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [A_3] : m1_subset_1(k2_subset_1(A_3),k1_zfmisc_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_79,plain,(
    ! [A_3] : m1_subset_1(A_3,k1_zfmisc_1(A_3)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_6])).

tff(c_74,plain,(
    ! [D_40] :
      ( r2_hidden('#skF_5',D_40)
      | ~ r2_hidden(D_40,'#skF_6')
      | ~ m1_subset_1(D_40,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_122,plain,(
    ! [D_53] :
      ( r2_hidden('#skF_5',D_53)
      | ~ r2_hidden(D_53,'#skF_6')
      | ~ m1_subset_1(D_53,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_74])).

tff(c_127,plain,
    ( r2_hidden('#skF_5',k2_struct_0('#skF_4'))
    | ~ r2_hidden(k2_struct_0('#skF_4'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_79,c_122])).

tff(c_135,plain,(
    ~ r2_hidden(k2_struct_0('#skF_4'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_127])).

tff(c_140,plain,(
    ! [A_57] :
      ( r2_hidden(u1_struct_0(A_57),u1_pre_topc(A_57))
      | ~ v2_pre_topc(A_57)
      | ~ l1_pre_topc(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_146,plain,
    ( r2_hidden(k2_struct_0('#skF_4'),u1_pre_topc('#skF_4'))
    | ~ v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_107,c_140])).

tff(c_149,plain,(
    r2_hidden(k2_struct_0('#skF_4'),u1_pre_topc('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_68,c_146])).

tff(c_208,plain,(
    ! [B_66,A_67] :
      ( v3_pre_topc(B_66,A_67)
      | ~ r2_hidden(B_66,u1_pre_topc(A_67))
      | ~ m1_subset_1(B_66,k1_zfmisc_1(u1_struct_0(A_67)))
      | ~ l1_pre_topc(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_219,plain,(
    ! [A_68] :
      ( v3_pre_topc(u1_struct_0(A_68),A_68)
      | ~ r2_hidden(u1_struct_0(A_68),u1_pre_topc(A_68))
      | ~ l1_pre_topc(A_68) ) ),
    inference(resolution,[status(thm)],[c_79,c_208])).

tff(c_231,plain,
    ( v3_pre_topc(u1_struct_0('#skF_4'),'#skF_4')
    | ~ r2_hidden(k2_struct_0('#skF_4'),u1_pre_topc('#skF_4'))
    | ~ l1_pre_topc('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_107,c_219])).

tff(c_236,plain,(
    v3_pre_topc(k2_struct_0('#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_149,c_107,c_231])).

tff(c_72,plain,(
    ! [D_40] :
      ( r2_hidden(D_40,'#skF_6')
      | ~ r2_hidden('#skF_5',D_40)
      | ~ v4_pre_topc(D_40,'#skF_4')
      | ~ v3_pre_topc(D_40,'#skF_4')
      | ~ m1_subset_1(D_40,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_244,plain,(
    ! [D_70] :
      ( r2_hidden(D_70,'#skF_6')
      | ~ r2_hidden('#skF_5',D_70)
      | ~ v4_pre_topc(D_70,'#skF_4')
      | ~ v3_pre_topc(D_70,'#skF_4')
      | ~ m1_subset_1(D_70,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_72])).

tff(c_248,plain,
    ( r2_hidden(k2_struct_0('#skF_4'),'#skF_6')
    | ~ r2_hidden('#skF_5',k2_struct_0('#skF_4'))
    | ~ v4_pre_topc(k2_struct_0('#skF_4'),'#skF_4')
    | ~ v3_pre_topc(k2_struct_0('#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_79,c_244])).

tff(c_251,plain,
    ( r2_hidden(k2_struct_0('#skF_4'),'#skF_6')
    | ~ r2_hidden('#skF_5',k2_struct_0('#skF_4'))
    | ~ v4_pre_topc(k2_struct_0('#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_236,c_248])).

tff(c_252,plain,
    ( ~ r2_hidden('#skF_5',k2_struct_0('#skF_4'))
    | ~ v4_pre_topc(k2_struct_0('#skF_4'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_135,c_251])).

tff(c_253,plain,(
    ~ v4_pre_topc(k2_struct_0('#skF_4'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_252])).

tff(c_256,plain,
    ( ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_253])).

tff(c_260,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_256])).

tff(c_261,plain,(
    ~ r2_hidden('#skF_5',k2_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_252])).

tff(c_265,plain,
    ( v1_xboole_0(k2_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_5',k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_8,c_261])).

tff(c_268,plain,(
    v1_xboole_0(k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_265])).

tff(c_58,plain,(
    ! [A_28] :
      ( ~ v1_xboole_0(k2_struct_0(A_28))
      | ~ l1_struct_0(A_28)
      | v2_struct_0(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_271,plain,
    ( ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_268,c_58])).

tff(c_274,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_271])).

tff(c_295,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_274])).

tff(c_299,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_295])).

tff(c_301,plain,(
    r2_hidden(k2_struct_0('#skF_4'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_127])).

tff(c_10,plain,(
    ! [B_7,A_6] :
      ( ~ r1_tarski(B_7,A_6)
      | ~ r2_hidden(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_308,plain,(
    ~ r1_tarski('#skF_6',k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_301,c_10])).

tff(c_312,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_308])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n001.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 16:04:45 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.56/1.47  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.56/1.48  
% 2.56/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.56/1.48  %$ v4_pre_topc > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k9_subset_1 > k5_setfam_1 > #nlpp > u1_struct_0 > u1_pre_topc > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_6 > #skF_4 > #skF_3
% 2.56/1.48  
% 2.56/1.48  %Foreground sorts:
% 2.56/1.48  
% 2.56/1.48  
% 2.56/1.48  %Background operators:
% 2.56/1.48  
% 2.56/1.48  
% 2.56/1.48  %Foreground operators:
% 2.56/1.48  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.56/1.48  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 2.56/1.48  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.56/1.48  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.56/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.56/1.48  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.56/1.48  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.56/1.48  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.56/1.48  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.56/1.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.56/1.48  tff('#skF_5', type, '#skF_5': $i).
% 2.56/1.48  tff('#skF_6', type, '#skF_6': $i).
% 2.56/1.48  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.56/1.48  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.56/1.48  tff(k5_setfam_1, type, k5_setfam_1: ($i * $i) > $i).
% 2.56/1.48  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.56/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.56/1.48  tff('#skF_4', type, '#skF_4': $i).
% 2.56/1.48  tff('#skF_3', type, '#skF_3': $i > $i).
% 2.56/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.56/1.48  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.56/1.48  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.56/1.48  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.56/1.48  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.56/1.48  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.56/1.48  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 2.56/1.48  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.56/1.48  
% 2.56/1.50  tff(f_126, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => ~((![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(D, C) <=> ((v3_pre_topc(D, A) & v4_pre_topc(D, A)) & r2_hidden(B, D))))) & (C = k1_xboole_0)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_connsp_2)).
% 2.56/1.50  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.56/1.50  tff(f_84, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.56/1.50  tff(f_71, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 2.56/1.50  tff(f_37, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 2.56/1.50  tff(f_90, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v4_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_pre_topc)).
% 2.56/1.50  tff(f_29, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 2.56/1.50  tff(f_31, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 2.56/1.50  tff(f_67, axiom, (![A]: (l1_pre_topc(A) => (v2_pre_topc(A) <=> ((r2_hidden(u1_struct_0(A), u1_pre_topc(A)) & (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (r1_tarski(B, u1_pre_topc(A)) => r2_hidden(k5_setfam_1(u1_struct_0(A), B), u1_pre_topc(A)))))) & (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r2_hidden(B, u1_pre_topc(A)) & r2_hidden(C, u1_pre_topc(A))) => r2_hidden(k9_subset_1(u1_struct_0(A), B, C), u1_pre_topc(A))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_pre_topc)).
% 2.56/1.50  tff(f_80, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> r2_hidden(B, u1_pre_topc(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_pre_topc)).
% 2.56/1.50  tff(f_98, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(k2_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc5_struct_0)).
% 2.56/1.50  tff(f_42, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.56/1.50  tff(c_60, plain, (k1_xboole_0='#skF_6'), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.56/1.50  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.56/1.50  tff(c_80, plain, (![A_1]: (r1_tarski('#skF_6', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_2])).
% 2.56/1.50  tff(c_66, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.56/1.50  tff(c_54, plain, (![A_26]: (l1_struct_0(A_26) | ~l1_pre_topc(A_26))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.56/1.50  tff(c_70, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.56/1.50  tff(c_97, plain, (![A_45]: (u1_struct_0(A_45)=k2_struct_0(A_45) | ~l1_struct_0(A_45))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.56/1.50  tff(c_103, plain, (![A_48]: (u1_struct_0(A_48)=k2_struct_0(A_48) | ~l1_pre_topc(A_48))), inference(resolution, [status(thm)], [c_54, c_97])).
% 2.56/1.50  tff(c_107, plain, (u1_struct_0('#skF_4')=k2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_66, c_103])).
% 2.56/1.50  tff(c_64, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.56/1.50  tff(c_109, plain, (m1_subset_1('#skF_5', k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_107, c_64])).
% 2.56/1.50  tff(c_8, plain, (![A_4, B_5]: (r2_hidden(A_4, B_5) | v1_xboole_0(B_5) | ~m1_subset_1(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.56/1.50  tff(c_68, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.56/1.50  tff(c_56, plain, (![A_27]: (v4_pre_topc(k2_struct_0(A_27), A_27) | ~l1_pre_topc(A_27) | ~v2_pre_topc(A_27))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.56/1.50  tff(c_4, plain, (![A_2]: (k2_subset_1(A_2)=A_2)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.56/1.50  tff(c_6, plain, (![A_3]: (m1_subset_1(k2_subset_1(A_3), k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.56/1.50  tff(c_79, plain, (![A_3]: (m1_subset_1(A_3, k1_zfmisc_1(A_3)))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_6])).
% 2.56/1.50  tff(c_74, plain, (![D_40]: (r2_hidden('#skF_5', D_40) | ~r2_hidden(D_40, '#skF_6') | ~m1_subset_1(D_40, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.56/1.50  tff(c_122, plain, (![D_53]: (r2_hidden('#skF_5', D_53) | ~r2_hidden(D_53, '#skF_6') | ~m1_subset_1(D_53, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_107, c_74])).
% 2.56/1.50  tff(c_127, plain, (r2_hidden('#skF_5', k2_struct_0('#skF_4')) | ~r2_hidden(k2_struct_0('#skF_4'), '#skF_6')), inference(resolution, [status(thm)], [c_79, c_122])).
% 2.56/1.50  tff(c_135, plain, (~r2_hidden(k2_struct_0('#skF_4'), '#skF_6')), inference(splitLeft, [status(thm)], [c_127])).
% 2.56/1.50  tff(c_140, plain, (![A_57]: (r2_hidden(u1_struct_0(A_57), u1_pre_topc(A_57)) | ~v2_pre_topc(A_57) | ~l1_pre_topc(A_57))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.56/1.50  tff(c_146, plain, (r2_hidden(k2_struct_0('#skF_4'), u1_pre_topc('#skF_4')) | ~v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_107, c_140])).
% 2.56/1.50  tff(c_149, plain, (r2_hidden(k2_struct_0('#skF_4'), u1_pre_topc('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_68, c_146])).
% 2.56/1.50  tff(c_208, plain, (![B_66, A_67]: (v3_pre_topc(B_66, A_67) | ~r2_hidden(B_66, u1_pre_topc(A_67)) | ~m1_subset_1(B_66, k1_zfmisc_1(u1_struct_0(A_67))) | ~l1_pre_topc(A_67))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.56/1.50  tff(c_219, plain, (![A_68]: (v3_pre_topc(u1_struct_0(A_68), A_68) | ~r2_hidden(u1_struct_0(A_68), u1_pre_topc(A_68)) | ~l1_pre_topc(A_68))), inference(resolution, [status(thm)], [c_79, c_208])).
% 2.56/1.50  tff(c_231, plain, (v3_pre_topc(u1_struct_0('#skF_4'), '#skF_4') | ~r2_hidden(k2_struct_0('#skF_4'), u1_pre_topc('#skF_4')) | ~l1_pre_topc('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_107, c_219])).
% 2.56/1.50  tff(c_236, plain, (v3_pre_topc(k2_struct_0('#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_149, c_107, c_231])).
% 2.56/1.50  tff(c_72, plain, (![D_40]: (r2_hidden(D_40, '#skF_6') | ~r2_hidden('#skF_5', D_40) | ~v4_pre_topc(D_40, '#skF_4') | ~v3_pre_topc(D_40, '#skF_4') | ~m1_subset_1(D_40, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.56/1.50  tff(c_244, plain, (![D_70]: (r2_hidden(D_70, '#skF_6') | ~r2_hidden('#skF_5', D_70) | ~v4_pre_topc(D_70, '#skF_4') | ~v3_pre_topc(D_70, '#skF_4') | ~m1_subset_1(D_70, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_107, c_72])).
% 2.56/1.50  tff(c_248, plain, (r2_hidden(k2_struct_0('#skF_4'), '#skF_6') | ~r2_hidden('#skF_5', k2_struct_0('#skF_4')) | ~v4_pre_topc(k2_struct_0('#skF_4'), '#skF_4') | ~v3_pre_topc(k2_struct_0('#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_79, c_244])).
% 2.56/1.50  tff(c_251, plain, (r2_hidden(k2_struct_0('#skF_4'), '#skF_6') | ~r2_hidden('#skF_5', k2_struct_0('#skF_4')) | ~v4_pre_topc(k2_struct_0('#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_236, c_248])).
% 2.56/1.50  tff(c_252, plain, (~r2_hidden('#skF_5', k2_struct_0('#skF_4')) | ~v4_pre_topc(k2_struct_0('#skF_4'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_135, c_251])).
% 2.56/1.50  tff(c_253, plain, (~v4_pre_topc(k2_struct_0('#skF_4'), '#skF_4')), inference(splitLeft, [status(thm)], [c_252])).
% 2.56/1.50  tff(c_256, plain, (~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_56, c_253])).
% 2.56/1.50  tff(c_260, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_256])).
% 2.56/1.50  tff(c_261, plain, (~r2_hidden('#skF_5', k2_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_252])).
% 2.56/1.50  tff(c_265, plain, (v1_xboole_0(k2_struct_0('#skF_4')) | ~m1_subset_1('#skF_5', k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_8, c_261])).
% 2.56/1.50  tff(c_268, plain, (v1_xboole_0(k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_109, c_265])).
% 2.56/1.50  tff(c_58, plain, (![A_28]: (~v1_xboole_0(k2_struct_0(A_28)) | ~l1_struct_0(A_28) | v2_struct_0(A_28))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.56/1.50  tff(c_271, plain, (~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_268, c_58])).
% 2.56/1.50  tff(c_274, plain, (~l1_struct_0('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_70, c_271])).
% 2.56/1.50  tff(c_295, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_54, c_274])).
% 2.56/1.50  tff(c_299, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_295])).
% 2.56/1.50  tff(c_301, plain, (r2_hidden(k2_struct_0('#skF_4'), '#skF_6')), inference(splitRight, [status(thm)], [c_127])).
% 2.56/1.50  tff(c_10, plain, (![B_7, A_6]: (~r1_tarski(B_7, A_6) | ~r2_hidden(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.56/1.50  tff(c_308, plain, (~r1_tarski('#skF_6', k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_301, c_10])).
% 2.56/1.50  tff(c_312, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_80, c_308])).
% 2.56/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.56/1.50  
% 2.56/1.50  Inference rules
% 2.56/1.50  ----------------------
% 2.56/1.50  #Ref     : 0
% 2.56/1.50  #Sup     : 42
% 2.56/1.50  #Fact    : 0
% 2.56/1.50  #Define  : 0
% 2.56/1.50  #Split   : 3
% 2.56/1.50  #Chain   : 0
% 2.56/1.50  #Close   : 0
% 2.56/1.50  
% 2.56/1.50  Ordering : KBO
% 2.56/1.50  
% 2.56/1.50  Simplification rules
% 2.56/1.50  ----------------------
% 2.56/1.50  #Subsume      : 5
% 2.56/1.50  #Demod        : 35
% 2.56/1.50  #Tautology    : 12
% 2.56/1.50  #SimpNegUnit  : 2
% 2.56/1.50  #BackRed      : 2
% 2.56/1.50  
% 2.56/1.50  #Partial instantiations: 0
% 2.56/1.50  #Strategies tried      : 1
% 2.56/1.50  
% 2.56/1.50  Timing (in seconds)
% 2.56/1.50  ----------------------
% 2.56/1.50  Preprocessing        : 0.42
% 2.56/1.50  Parsing              : 0.21
% 2.56/1.50  CNF conversion       : 0.03
% 2.56/1.50  Main loop            : 0.22
% 2.56/1.50  Inferencing          : 0.07
% 2.56/1.50  Reduction            : 0.07
% 2.56/1.50  Demodulation         : 0.05
% 2.56/1.50  BG Simplification    : 0.02
% 2.56/1.50  Subsumption          : 0.04
% 2.56/1.50  Abstraction          : 0.01
% 2.56/1.50  MUC search           : 0.00
% 2.56/1.50  Cooper               : 0.00
% 2.56/1.50  Total                : 0.67
% 2.56/1.50  Index Insertion      : 0.00
% 2.56/1.50  Index Deletion       : 0.00
% 2.56/1.50  Index Matching       : 0.00
% 2.56/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
