%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:23 EST 2020

% Result     : Theorem 2.36s
% Output     : CNFRefutation 2.65s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 272 expanded)
%              Number of leaves         :   39 ( 108 expanded)
%              Depth                    :   12
%              Number of atoms          :  142 ( 723 expanded)
%              Number of equality atoms :    8 (  99 expanded)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_connsp_2)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_98,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v4_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_pre_topc)).

tff(f_84,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_71,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_92,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_29,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_31,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_pre_topc)).

tff(f_80,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_pre_topc(B,A)
          <=> r2_hidden(B,u1_pre_topc(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_pre_topc)).

tff(f_42,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_60,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_80,plain,(
    ! [A_1] : r1_tarski('#skF_6',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_2])).

tff(c_68,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_66,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_58,plain,(
    ! [A_28] :
      ( v4_pre_topc(k2_struct_0(A_28),A_28)
      | ~ l1_pre_topc(A_28)
      | ~ v2_pre_topc(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

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

tff(c_114,plain,(
    ! [A_49] :
      ( ~ v1_xboole_0(u1_struct_0(A_49))
      | ~ l1_struct_0(A_49)
      | v2_struct_0(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_117,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_4'))
    | ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_107,c_114])).

tff(c_118,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_4'))
    | ~ l1_struct_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_117])).

tff(c_119,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_118])).

tff(c_122,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_119])).

tff(c_126,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_122])).

tff(c_127,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_118])).

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

tff(c_135,plain,(
    ! [D_50] :
      ( r2_hidden('#skF_5',D_50)
      | ~ r2_hidden(D_50,'#skF_6')
      | ~ m1_subset_1(D_50,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_74])).

tff(c_140,plain,
    ( r2_hidden('#skF_5',k2_struct_0('#skF_4'))
    | ~ r2_hidden(k2_struct_0('#skF_4'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_79,c_135])).

tff(c_175,plain,(
    ~ r2_hidden(k2_struct_0('#skF_4'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_140])).

tff(c_72,plain,(
    ! [D_40] :
      ( r2_hidden(D_40,'#skF_6')
      | ~ r2_hidden('#skF_5',D_40)
      | ~ v4_pre_topc(D_40,'#skF_4')
      | ~ v3_pre_topc(D_40,'#skF_4')
      | ~ m1_subset_1(D_40,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_221,plain,(
    ! [D_65] :
      ( r2_hidden(D_65,'#skF_6')
      | ~ r2_hidden('#skF_5',D_65)
      | ~ v4_pre_topc(D_65,'#skF_4')
      | ~ v3_pre_topc(D_65,'#skF_4')
      | ~ m1_subset_1(D_65,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_72])).

tff(c_225,plain,
    ( r2_hidden(k2_struct_0('#skF_4'),'#skF_6')
    | ~ r2_hidden('#skF_5',k2_struct_0('#skF_4'))
    | ~ v4_pre_topc(k2_struct_0('#skF_4'),'#skF_4')
    | ~ v3_pre_topc(k2_struct_0('#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_79,c_221])).

tff(c_228,plain,
    ( ~ r2_hidden('#skF_5',k2_struct_0('#skF_4'))
    | ~ v4_pre_topc(k2_struct_0('#skF_4'),'#skF_4')
    | ~ v3_pre_topc(k2_struct_0('#skF_4'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_175,c_225])).

tff(c_236,plain,(
    ~ v3_pre_topc(k2_struct_0('#skF_4'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_228])).

tff(c_152,plain,(
    ! [A_56] :
      ( r2_hidden(u1_struct_0(A_56),u1_pre_topc(A_56))
      | ~ v2_pre_topc(A_56)
      | ~ l1_pre_topc(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_158,plain,
    ( r2_hidden(k2_struct_0('#skF_4'),u1_pre_topc('#skF_4'))
    | ~ v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_107,c_152])).

tff(c_161,plain,(
    r2_hidden(k2_struct_0('#skF_4'),u1_pre_topc('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_68,c_158])).

tff(c_237,plain,(
    ! [B_67,A_68] :
      ( v3_pre_topc(B_67,A_68)
      | ~ r2_hidden(B_67,u1_pre_topc(A_68))
      | ~ m1_subset_1(B_67,k1_zfmisc_1(u1_struct_0(A_68)))
      | ~ l1_pre_topc(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_248,plain,(
    ! [A_69] :
      ( v3_pre_topc(u1_struct_0(A_69),A_69)
      | ~ r2_hidden(u1_struct_0(A_69),u1_pre_topc(A_69))
      | ~ l1_pre_topc(A_69) ) ),
    inference(resolution,[status(thm)],[c_79,c_237])).

tff(c_260,plain,
    ( v3_pre_topc(u1_struct_0('#skF_4'),'#skF_4')
    | ~ r2_hidden(k2_struct_0('#skF_4'),u1_pre_topc('#skF_4'))
    | ~ l1_pre_topc('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_107,c_248])).

tff(c_265,plain,(
    v3_pre_topc(k2_struct_0('#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_161,c_107,c_260])).

tff(c_267,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_236,c_265])).

tff(c_268,plain,
    ( ~ v4_pre_topc(k2_struct_0('#skF_4'),'#skF_4')
    | ~ r2_hidden('#skF_5',k2_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_228])).

tff(c_281,plain,(
    ~ r2_hidden('#skF_5',k2_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_268])).

tff(c_284,plain,
    ( v1_xboole_0(k2_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_5',k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_8,c_281])).

tff(c_287,plain,(
    v1_xboole_0(k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_284])).

tff(c_289,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_127,c_287])).

tff(c_290,plain,(
    ~ v4_pre_topc(k2_struct_0('#skF_4'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_268])).

tff(c_306,plain,
    ( ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_290])).

tff(c_310,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_306])).

tff(c_312,plain,(
    r2_hidden(k2_struct_0('#skF_4'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_140])).

tff(c_10,plain,(
    ! [B_7,A_6] :
      ( ~ r1_tarski(B_7,A_6)
      | ~ r2_hidden(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_319,plain,(
    ~ r1_tarski('#skF_6',k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_312,c_10])).

tff(c_323,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_319])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.32  % Computer   : n014.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 20:49:07 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.36/1.35  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.36/1.36  
% 2.36/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.36/1.36  %$ v4_pre_topc > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k9_subset_1 > k5_setfam_1 > #nlpp > u1_struct_0 > u1_pre_topc > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_6 > #skF_4 > #skF_3
% 2.36/1.36  
% 2.36/1.36  %Foreground sorts:
% 2.36/1.36  
% 2.36/1.36  
% 2.36/1.36  %Background operators:
% 2.36/1.36  
% 2.36/1.36  
% 2.36/1.36  %Foreground operators:
% 2.36/1.36  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.36/1.36  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 2.36/1.36  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.36/1.36  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.36/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.36/1.36  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.36/1.36  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.36/1.36  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.36/1.36  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.36/1.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.36/1.36  tff('#skF_5', type, '#skF_5': $i).
% 2.36/1.36  tff('#skF_6', type, '#skF_6': $i).
% 2.36/1.36  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.36/1.36  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.36/1.36  tff(k5_setfam_1, type, k5_setfam_1: ($i * $i) > $i).
% 2.36/1.36  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.36/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.36/1.36  tff('#skF_4', type, '#skF_4': $i).
% 2.36/1.36  tff('#skF_3', type, '#skF_3': $i > $i).
% 2.36/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.36/1.36  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.36/1.36  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.36/1.36  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.36/1.36  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.36/1.36  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.36/1.36  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 2.36/1.36  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.36/1.36  
% 2.65/1.38  tff(f_126, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => ~((![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(D, C) <=> ((v3_pre_topc(D, A) & v4_pre_topc(D, A)) & r2_hidden(B, D))))) & (C = k1_xboole_0)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_connsp_2)).
% 2.65/1.38  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.65/1.38  tff(f_98, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v4_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_pre_topc)).
% 2.65/1.38  tff(f_84, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.65/1.38  tff(f_71, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 2.65/1.38  tff(f_92, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.65/1.38  tff(f_37, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 2.65/1.38  tff(f_29, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 2.65/1.38  tff(f_31, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 2.65/1.38  tff(f_67, axiom, (![A]: (l1_pre_topc(A) => (v2_pre_topc(A) <=> ((r2_hidden(u1_struct_0(A), u1_pre_topc(A)) & (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (r1_tarski(B, u1_pre_topc(A)) => r2_hidden(k5_setfam_1(u1_struct_0(A), B), u1_pre_topc(A)))))) & (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r2_hidden(B, u1_pre_topc(A)) & r2_hidden(C, u1_pre_topc(A))) => r2_hidden(k9_subset_1(u1_struct_0(A), B, C), u1_pre_topc(A))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_pre_topc)).
% 2.65/1.38  tff(f_80, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> r2_hidden(B, u1_pre_topc(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_pre_topc)).
% 2.65/1.38  tff(f_42, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.65/1.38  tff(c_60, plain, (k1_xboole_0='#skF_6'), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.65/1.38  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.65/1.38  tff(c_80, plain, (![A_1]: (r1_tarski('#skF_6', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_2])).
% 2.65/1.38  tff(c_68, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.65/1.38  tff(c_66, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.65/1.38  tff(c_58, plain, (![A_28]: (v4_pre_topc(k2_struct_0(A_28), A_28) | ~l1_pre_topc(A_28) | ~v2_pre_topc(A_28))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.65/1.38  tff(c_54, plain, (![A_26]: (l1_struct_0(A_26) | ~l1_pre_topc(A_26))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.65/1.38  tff(c_70, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.65/1.38  tff(c_97, plain, (![A_45]: (u1_struct_0(A_45)=k2_struct_0(A_45) | ~l1_struct_0(A_45))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.65/1.38  tff(c_103, plain, (![A_48]: (u1_struct_0(A_48)=k2_struct_0(A_48) | ~l1_pre_topc(A_48))), inference(resolution, [status(thm)], [c_54, c_97])).
% 2.65/1.38  tff(c_107, plain, (u1_struct_0('#skF_4')=k2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_66, c_103])).
% 2.65/1.38  tff(c_114, plain, (![A_49]: (~v1_xboole_0(u1_struct_0(A_49)) | ~l1_struct_0(A_49) | v2_struct_0(A_49))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.65/1.38  tff(c_117, plain, (~v1_xboole_0(k2_struct_0('#skF_4')) | ~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_107, c_114])).
% 2.65/1.38  tff(c_118, plain, (~v1_xboole_0(k2_struct_0('#skF_4')) | ~l1_struct_0('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_70, c_117])).
% 2.65/1.38  tff(c_119, plain, (~l1_struct_0('#skF_4')), inference(splitLeft, [status(thm)], [c_118])).
% 2.65/1.38  tff(c_122, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_54, c_119])).
% 2.65/1.38  tff(c_126, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_122])).
% 2.65/1.38  tff(c_127, plain, (~v1_xboole_0(k2_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_118])).
% 2.65/1.38  tff(c_64, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.65/1.38  tff(c_109, plain, (m1_subset_1('#skF_5', k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_107, c_64])).
% 2.65/1.38  tff(c_8, plain, (![A_4, B_5]: (r2_hidden(A_4, B_5) | v1_xboole_0(B_5) | ~m1_subset_1(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.65/1.38  tff(c_4, plain, (![A_2]: (k2_subset_1(A_2)=A_2)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.65/1.38  tff(c_6, plain, (![A_3]: (m1_subset_1(k2_subset_1(A_3), k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.65/1.38  tff(c_79, plain, (![A_3]: (m1_subset_1(A_3, k1_zfmisc_1(A_3)))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_6])).
% 2.65/1.38  tff(c_74, plain, (![D_40]: (r2_hidden('#skF_5', D_40) | ~r2_hidden(D_40, '#skF_6') | ~m1_subset_1(D_40, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.65/1.38  tff(c_135, plain, (![D_50]: (r2_hidden('#skF_5', D_50) | ~r2_hidden(D_50, '#skF_6') | ~m1_subset_1(D_50, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_107, c_74])).
% 2.65/1.38  tff(c_140, plain, (r2_hidden('#skF_5', k2_struct_0('#skF_4')) | ~r2_hidden(k2_struct_0('#skF_4'), '#skF_6')), inference(resolution, [status(thm)], [c_79, c_135])).
% 2.65/1.38  tff(c_175, plain, (~r2_hidden(k2_struct_0('#skF_4'), '#skF_6')), inference(splitLeft, [status(thm)], [c_140])).
% 2.65/1.38  tff(c_72, plain, (![D_40]: (r2_hidden(D_40, '#skF_6') | ~r2_hidden('#skF_5', D_40) | ~v4_pre_topc(D_40, '#skF_4') | ~v3_pre_topc(D_40, '#skF_4') | ~m1_subset_1(D_40, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.65/1.38  tff(c_221, plain, (![D_65]: (r2_hidden(D_65, '#skF_6') | ~r2_hidden('#skF_5', D_65) | ~v4_pre_topc(D_65, '#skF_4') | ~v3_pre_topc(D_65, '#skF_4') | ~m1_subset_1(D_65, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_107, c_72])).
% 2.65/1.38  tff(c_225, plain, (r2_hidden(k2_struct_0('#skF_4'), '#skF_6') | ~r2_hidden('#skF_5', k2_struct_0('#skF_4')) | ~v4_pre_topc(k2_struct_0('#skF_4'), '#skF_4') | ~v3_pre_topc(k2_struct_0('#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_79, c_221])).
% 2.65/1.38  tff(c_228, plain, (~r2_hidden('#skF_5', k2_struct_0('#skF_4')) | ~v4_pre_topc(k2_struct_0('#skF_4'), '#skF_4') | ~v3_pre_topc(k2_struct_0('#skF_4'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_175, c_225])).
% 2.65/1.38  tff(c_236, plain, (~v3_pre_topc(k2_struct_0('#skF_4'), '#skF_4')), inference(splitLeft, [status(thm)], [c_228])).
% 2.65/1.38  tff(c_152, plain, (![A_56]: (r2_hidden(u1_struct_0(A_56), u1_pre_topc(A_56)) | ~v2_pre_topc(A_56) | ~l1_pre_topc(A_56))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.65/1.38  tff(c_158, plain, (r2_hidden(k2_struct_0('#skF_4'), u1_pre_topc('#skF_4')) | ~v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_107, c_152])).
% 2.65/1.38  tff(c_161, plain, (r2_hidden(k2_struct_0('#skF_4'), u1_pre_topc('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_68, c_158])).
% 2.65/1.38  tff(c_237, plain, (![B_67, A_68]: (v3_pre_topc(B_67, A_68) | ~r2_hidden(B_67, u1_pre_topc(A_68)) | ~m1_subset_1(B_67, k1_zfmisc_1(u1_struct_0(A_68))) | ~l1_pre_topc(A_68))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.65/1.38  tff(c_248, plain, (![A_69]: (v3_pre_topc(u1_struct_0(A_69), A_69) | ~r2_hidden(u1_struct_0(A_69), u1_pre_topc(A_69)) | ~l1_pre_topc(A_69))), inference(resolution, [status(thm)], [c_79, c_237])).
% 2.65/1.38  tff(c_260, plain, (v3_pre_topc(u1_struct_0('#skF_4'), '#skF_4') | ~r2_hidden(k2_struct_0('#skF_4'), u1_pre_topc('#skF_4')) | ~l1_pre_topc('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_107, c_248])).
% 2.65/1.38  tff(c_265, plain, (v3_pre_topc(k2_struct_0('#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_161, c_107, c_260])).
% 2.65/1.38  tff(c_267, plain, $false, inference(negUnitSimplification, [status(thm)], [c_236, c_265])).
% 2.65/1.38  tff(c_268, plain, (~v4_pre_topc(k2_struct_0('#skF_4'), '#skF_4') | ~r2_hidden('#skF_5', k2_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_228])).
% 2.65/1.38  tff(c_281, plain, (~r2_hidden('#skF_5', k2_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_268])).
% 2.65/1.38  tff(c_284, plain, (v1_xboole_0(k2_struct_0('#skF_4')) | ~m1_subset_1('#skF_5', k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_8, c_281])).
% 2.65/1.38  tff(c_287, plain, (v1_xboole_0(k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_109, c_284])).
% 2.65/1.38  tff(c_289, plain, $false, inference(negUnitSimplification, [status(thm)], [c_127, c_287])).
% 2.65/1.38  tff(c_290, plain, (~v4_pre_topc(k2_struct_0('#skF_4'), '#skF_4')), inference(splitRight, [status(thm)], [c_268])).
% 2.65/1.38  tff(c_306, plain, (~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_58, c_290])).
% 2.65/1.38  tff(c_310, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_306])).
% 2.65/1.38  tff(c_312, plain, (r2_hidden(k2_struct_0('#skF_4'), '#skF_6')), inference(splitRight, [status(thm)], [c_140])).
% 2.65/1.38  tff(c_10, plain, (![B_7, A_6]: (~r1_tarski(B_7, A_6) | ~r2_hidden(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.65/1.38  tff(c_319, plain, (~r1_tarski('#skF_6', k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_312, c_10])).
% 2.65/1.38  tff(c_323, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_80, c_319])).
% 2.65/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.65/1.38  
% 2.65/1.38  Inference rules
% 2.65/1.38  ----------------------
% 2.65/1.38  #Ref     : 0
% 2.65/1.38  #Sup     : 42
% 2.65/1.38  #Fact    : 0
% 2.65/1.38  #Define  : 0
% 2.65/1.38  #Split   : 5
% 2.65/1.38  #Chain   : 0
% 2.65/1.38  #Close   : 0
% 2.65/1.38  
% 2.65/1.38  Ordering : KBO
% 2.65/1.38  
% 2.65/1.38  Simplification rules
% 2.65/1.38  ----------------------
% 2.65/1.38  #Subsume      : 5
% 2.65/1.38  #Demod        : 32
% 2.65/1.38  #Tautology    : 11
% 2.65/1.38  #SimpNegUnit  : 4
% 2.65/1.38  #BackRed      : 2
% 2.65/1.38  
% 2.65/1.38  #Partial instantiations: 0
% 2.65/1.38  #Strategies tried      : 1
% 2.65/1.38  
% 2.65/1.38  Timing (in seconds)
% 2.65/1.38  ----------------------
% 2.65/1.39  Preprocessing        : 0.35
% 2.65/1.39  Parsing              : 0.19
% 2.65/1.39  CNF conversion       : 0.03
% 2.65/1.39  Main loop            : 0.22
% 2.65/1.39  Inferencing          : 0.07
% 2.65/1.39  Reduction            : 0.07
% 2.65/1.39  Demodulation         : 0.05
% 2.65/1.39  BG Simplification    : 0.02
% 2.65/1.39  Subsumption          : 0.04
% 2.65/1.39  Abstraction          : 0.01
% 2.65/1.39  MUC search           : 0.00
% 2.65/1.39  Cooper               : 0.00
% 2.65/1.39  Total                : 0.62
% 2.65/1.39  Index Insertion      : 0.00
% 2.65/1.39  Index Deletion       : 0.00
% 2.65/1.39  Index Matching       : 0.00
% 2.65/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
