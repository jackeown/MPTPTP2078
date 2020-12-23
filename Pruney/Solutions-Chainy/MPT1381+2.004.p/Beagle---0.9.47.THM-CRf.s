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
% DateTime   : Thu Dec  3 10:24:07 EST 2020

% Result     : Theorem 2.66s
% Output     : CNFRefutation 2.66s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 129 expanded)
%              Number of leaves         :   24 (  56 expanded)
%              Depth                    :   10
%              Number of atoms          :  141 ( 384 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_connsp_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(m1_connsp_2,type,(
    m1_connsp_2: ( $i * $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_104,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ( m1_connsp_2(B,A,C)
                 => r2_hidden(C,B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_connsp_2)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_55,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_72,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( m1_connsp_2(C,A,B)
              <=> r2_hidden(B,k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_connsp_2)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(c_26,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_33,plain,(
    ! [A_29,B_30] :
      ( r1_tarski(A_29,B_30)
      | ~ m1_subset_1(A_29,k1_zfmisc_1(B_30)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_37,plain,(
    r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_26,c_33])).

tff(c_28,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_43,plain,(
    ! [A_33,B_34] :
      ( r2_hidden(A_33,B_34)
      | v1_xboole_0(B_34)
      | ~ m1_subset_1(A_33,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_20,plain,(
    ~ r2_hidden('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_47,plain,
    ( v1_xboole_0('#skF_2')
    | ~ m1_subset_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_43,c_20])).

tff(c_48,plain,(
    ~ m1_subset_1('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_47])).

tff(c_22,plain,(
    m1_connsp_2('#skF_2','#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_24,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(A_3,k1_zfmisc_1(B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_69,plain,(
    ! [A_45,B_46] :
      ( r1_tarski(k1_tops_1(A_45,B_46),B_46)
      | ~ m1_subset_1(B_46,k1_zfmisc_1(u1_struct_0(A_45)))
      | ~ l1_pre_topc(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_75,plain,(
    ! [A_45,A_3] :
      ( r1_tarski(k1_tops_1(A_45,A_3),A_3)
      | ~ l1_pre_topc(A_45)
      | ~ r1_tarski(A_3,u1_struct_0(A_45)) ) ),
    inference(resolution,[status(thm)],[c_6,c_69])).

tff(c_32,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_30,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_188,plain,(
    ! [B_80,A_81,C_82] :
      ( r2_hidden(B_80,k1_tops_1(A_81,C_82))
      | ~ m1_connsp_2(C_82,A_81,B_80)
      | ~ m1_subset_1(C_82,k1_zfmisc_1(u1_struct_0(A_81)))
      | ~ m1_subset_1(B_80,u1_struct_0(A_81))
      | ~ l1_pre_topc(A_81)
      | ~ v2_pre_topc(A_81)
      | v2_struct_0(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_193,plain,(
    ! [B_80] :
      ( r2_hidden(B_80,k1_tops_1('#skF_1','#skF_2'))
      | ~ m1_connsp_2('#skF_2','#skF_1',B_80)
      | ~ m1_subset_1(B_80,u1_struct_0('#skF_1'))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_26,c_188])).

tff(c_197,plain,(
    ! [B_80] :
      ( r2_hidden(B_80,k1_tops_1('#skF_1','#skF_2'))
      | ~ m1_connsp_2('#skF_2','#skF_1',B_80)
      | ~ m1_subset_1(B_80,u1_struct_0('#skF_1'))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_193])).

tff(c_199,plain,(
    ! [B_83] :
      ( r2_hidden(B_83,k1_tops_1('#skF_1','#skF_2'))
      | ~ m1_connsp_2('#skF_2','#skF_1',B_83)
      | ~ m1_subset_1(B_83,u1_struct_0('#skF_1')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_197])).

tff(c_57,plain,(
    ! [A_38,C_39,B_40] :
      ( m1_subset_1(A_38,C_39)
      | ~ m1_subset_1(B_40,k1_zfmisc_1(C_39))
      | ~ r2_hidden(A_38,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_62,plain,(
    ! [A_38,B_4,A_3] :
      ( m1_subset_1(A_38,B_4)
      | ~ r2_hidden(A_38,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(resolution,[status(thm)],[c_6,c_57])).

tff(c_246,plain,(
    ! [B_88,B_89] :
      ( m1_subset_1(B_88,B_89)
      | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),B_89)
      | ~ m1_connsp_2('#skF_2','#skF_1',B_88)
      | ~ m1_subset_1(B_88,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_199,c_62])).

tff(c_249,plain,(
    ! [B_88] :
      ( m1_subset_1(B_88,'#skF_2')
      | ~ m1_connsp_2('#skF_2','#skF_1',B_88)
      | ~ m1_subset_1(B_88,u1_struct_0('#skF_1'))
      | ~ l1_pre_topc('#skF_1')
      | ~ r1_tarski('#skF_2',u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_75,c_246])).

tff(c_256,plain,(
    ! [B_90] :
      ( m1_subset_1(B_90,'#skF_2')
      | ~ m1_connsp_2('#skF_2','#skF_1',B_90)
      | ~ m1_subset_1(B_90,u1_struct_0('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_37,c_28,c_249])).

tff(c_265,plain,
    ( m1_subset_1('#skF_3','#skF_2')
    | ~ m1_connsp_2('#skF_2','#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_256])).

tff(c_270,plain,(
    m1_subset_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_265])).

tff(c_272,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_270])).

tff(c_273,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_47])).

tff(c_309,plain,(
    ! [A_110,B_111] :
      ( r1_tarski(k1_tops_1(A_110,B_111),B_111)
      | ~ m1_subset_1(B_111,k1_zfmisc_1(u1_struct_0(A_110)))
      | ~ l1_pre_topc(A_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_315,plain,(
    ! [A_110,A_3] :
      ( r1_tarski(k1_tops_1(A_110,A_3),A_3)
      | ~ l1_pre_topc(A_110)
      | ~ r1_tarski(A_3,u1_struct_0(A_110)) ) ),
    inference(resolution,[status(thm)],[c_6,c_309])).

tff(c_350,plain,(
    ! [B_127,A_128,C_129] :
      ( r2_hidden(B_127,k1_tops_1(A_128,C_129))
      | ~ m1_connsp_2(C_129,A_128,B_127)
      | ~ m1_subset_1(C_129,k1_zfmisc_1(u1_struct_0(A_128)))
      | ~ m1_subset_1(B_127,u1_struct_0(A_128))
      | ~ l1_pre_topc(A_128)
      | ~ v2_pre_topc(A_128)
      | v2_struct_0(A_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_355,plain,(
    ! [B_127] :
      ( r2_hidden(B_127,k1_tops_1('#skF_1','#skF_2'))
      | ~ m1_connsp_2('#skF_2','#skF_1',B_127)
      | ~ m1_subset_1(B_127,u1_struct_0('#skF_1'))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_26,c_350])).

tff(c_359,plain,(
    ! [B_127] :
      ( r2_hidden(B_127,k1_tops_1('#skF_1','#skF_2'))
      | ~ m1_connsp_2('#skF_2','#skF_1',B_127)
      | ~ m1_subset_1(B_127,u1_struct_0('#skF_1'))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_355])).

tff(c_361,plain,(
    ! [B_130] :
      ( r2_hidden(B_130,k1_tops_1('#skF_1','#skF_2'))
      | ~ m1_connsp_2('#skF_2','#skF_1',B_130)
      | ~ m1_subset_1(B_130,u1_struct_0('#skF_1')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_359])).

tff(c_275,plain,(
    ! [C_91,B_92,A_93] :
      ( ~ v1_xboole_0(C_91)
      | ~ m1_subset_1(B_92,k1_zfmisc_1(C_91))
      | ~ r2_hidden(A_93,B_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_280,plain,(
    ! [B_4,A_93,A_3] :
      ( ~ v1_xboole_0(B_4)
      | ~ r2_hidden(A_93,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(resolution,[status(thm)],[c_6,c_275])).

tff(c_373,plain,(
    ! [B_4,B_130] :
      ( ~ v1_xboole_0(B_4)
      | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),B_4)
      | ~ m1_connsp_2('#skF_2','#skF_1',B_130)
      | ~ m1_subset_1(B_130,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_361,c_280])).

tff(c_375,plain,(
    ! [B_131] :
      ( ~ m1_connsp_2('#skF_2','#skF_1',B_131)
      | ~ m1_subset_1(B_131,u1_struct_0('#skF_1')) ) ),
    inference(splitLeft,[status(thm)],[c_373])).

tff(c_381,plain,(
    ~ m1_connsp_2('#skF_2','#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_375])).

tff(c_386,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_381])).

tff(c_398,plain,(
    ! [B_134] :
      ( ~ v1_xboole_0(B_134)
      | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),B_134) ) ),
    inference(splitRight,[status(thm)],[c_373])).

tff(c_402,plain,
    ( ~ v1_xboole_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_315,c_398])).

tff(c_409,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_37,c_28,c_273,c_402])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:43:19 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.66/1.37  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.66/1.37  
% 2.66/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.66/1.38  %$ m1_connsp_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 2.66/1.38  
% 2.66/1.38  %Foreground sorts:
% 2.66/1.38  
% 2.66/1.38  
% 2.66/1.38  %Background operators:
% 2.66/1.38  
% 2.66/1.38  
% 2.66/1.38  %Foreground operators:
% 2.66/1.38  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.66/1.38  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 2.66/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.66/1.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.66/1.38  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.66/1.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.66/1.38  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 2.66/1.38  tff('#skF_2', type, '#skF_2': $i).
% 2.66/1.38  tff('#skF_3', type, '#skF_3': $i).
% 2.66/1.38  tff('#skF_1', type, '#skF_1': $i).
% 2.66/1.38  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.66/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.66/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.66/1.38  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.66/1.38  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.66/1.38  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.66/1.38  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.66/1.38  
% 2.66/1.39  tff(f_104, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (m1_connsp_2(B, A, C) => r2_hidden(C, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_connsp_2)).
% 2.66/1.39  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.66/1.39  tff(f_31, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 2.66/1.39  tff(f_55, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tops_1)).
% 2.66/1.39  tff(f_72, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m1_connsp_2(C, A, B) <=> r2_hidden(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_connsp_2)).
% 2.66/1.39  tff(f_41, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 2.66/1.39  tff(f_48, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 2.66/1.39  tff(c_26, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.66/1.39  tff(c_33, plain, (![A_29, B_30]: (r1_tarski(A_29, B_30) | ~m1_subset_1(A_29, k1_zfmisc_1(B_30)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.66/1.39  tff(c_37, plain, (r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_26, c_33])).
% 2.66/1.39  tff(c_28, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.66/1.39  tff(c_43, plain, (![A_33, B_34]: (r2_hidden(A_33, B_34) | v1_xboole_0(B_34) | ~m1_subset_1(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.66/1.39  tff(c_20, plain, (~r2_hidden('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.66/1.39  tff(c_47, plain, (v1_xboole_0('#skF_2') | ~m1_subset_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_43, c_20])).
% 2.66/1.39  tff(c_48, plain, (~m1_subset_1('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_47])).
% 2.66/1.39  tff(c_22, plain, (m1_connsp_2('#skF_2', '#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.66/1.39  tff(c_24, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.66/1.39  tff(c_6, plain, (![A_3, B_4]: (m1_subset_1(A_3, k1_zfmisc_1(B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.66/1.39  tff(c_69, plain, (![A_45, B_46]: (r1_tarski(k1_tops_1(A_45, B_46), B_46) | ~m1_subset_1(B_46, k1_zfmisc_1(u1_struct_0(A_45))) | ~l1_pre_topc(A_45))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.66/1.39  tff(c_75, plain, (![A_45, A_3]: (r1_tarski(k1_tops_1(A_45, A_3), A_3) | ~l1_pre_topc(A_45) | ~r1_tarski(A_3, u1_struct_0(A_45)))), inference(resolution, [status(thm)], [c_6, c_69])).
% 2.66/1.39  tff(c_32, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.66/1.39  tff(c_30, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.66/1.39  tff(c_188, plain, (![B_80, A_81, C_82]: (r2_hidden(B_80, k1_tops_1(A_81, C_82)) | ~m1_connsp_2(C_82, A_81, B_80) | ~m1_subset_1(C_82, k1_zfmisc_1(u1_struct_0(A_81))) | ~m1_subset_1(B_80, u1_struct_0(A_81)) | ~l1_pre_topc(A_81) | ~v2_pre_topc(A_81) | v2_struct_0(A_81))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.66/1.39  tff(c_193, plain, (![B_80]: (r2_hidden(B_80, k1_tops_1('#skF_1', '#skF_2')) | ~m1_connsp_2('#skF_2', '#skF_1', B_80) | ~m1_subset_1(B_80, u1_struct_0('#skF_1')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_26, c_188])).
% 2.66/1.39  tff(c_197, plain, (![B_80]: (r2_hidden(B_80, k1_tops_1('#skF_1', '#skF_2')) | ~m1_connsp_2('#skF_2', '#skF_1', B_80) | ~m1_subset_1(B_80, u1_struct_0('#skF_1')) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_193])).
% 2.66/1.39  tff(c_199, plain, (![B_83]: (r2_hidden(B_83, k1_tops_1('#skF_1', '#skF_2')) | ~m1_connsp_2('#skF_2', '#skF_1', B_83) | ~m1_subset_1(B_83, u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_32, c_197])).
% 2.66/1.39  tff(c_57, plain, (![A_38, C_39, B_40]: (m1_subset_1(A_38, C_39) | ~m1_subset_1(B_40, k1_zfmisc_1(C_39)) | ~r2_hidden(A_38, B_40))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.66/1.39  tff(c_62, plain, (![A_38, B_4, A_3]: (m1_subset_1(A_38, B_4) | ~r2_hidden(A_38, A_3) | ~r1_tarski(A_3, B_4))), inference(resolution, [status(thm)], [c_6, c_57])).
% 2.66/1.39  tff(c_246, plain, (![B_88, B_89]: (m1_subset_1(B_88, B_89) | ~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), B_89) | ~m1_connsp_2('#skF_2', '#skF_1', B_88) | ~m1_subset_1(B_88, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_199, c_62])).
% 2.66/1.39  tff(c_249, plain, (![B_88]: (m1_subset_1(B_88, '#skF_2') | ~m1_connsp_2('#skF_2', '#skF_1', B_88) | ~m1_subset_1(B_88, u1_struct_0('#skF_1')) | ~l1_pre_topc('#skF_1') | ~r1_tarski('#skF_2', u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_75, c_246])).
% 2.66/1.39  tff(c_256, plain, (![B_90]: (m1_subset_1(B_90, '#skF_2') | ~m1_connsp_2('#skF_2', '#skF_1', B_90) | ~m1_subset_1(B_90, u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_37, c_28, c_249])).
% 2.66/1.39  tff(c_265, plain, (m1_subset_1('#skF_3', '#skF_2') | ~m1_connsp_2('#skF_2', '#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_24, c_256])).
% 2.66/1.39  tff(c_270, plain, (m1_subset_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_265])).
% 2.66/1.39  tff(c_272, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_270])).
% 2.66/1.39  tff(c_273, plain, (v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_47])).
% 2.66/1.39  tff(c_309, plain, (![A_110, B_111]: (r1_tarski(k1_tops_1(A_110, B_111), B_111) | ~m1_subset_1(B_111, k1_zfmisc_1(u1_struct_0(A_110))) | ~l1_pre_topc(A_110))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.66/1.39  tff(c_315, plain, (![A_110, A_3]: (r1_tarski(k1_tops_1(A_110, A_3), A_3) | ~l1_pre_topc(A_110) | ~r1_tarski(A_3, u1_struct_0(A_110)))), inference(resolution, [status(thm)], [c_6, c_309])).
% 2.66/1.39  tff(c_350, plain, (![B_127, A_128, C_129]: (r2_hidden(B_127, k1_tops_1(A_128, C_129)) | ~m1_connsp_2(C_129, A_128, B_127) | ~m1_subset_1(C_129, k1_zfmisc_1(u1_struct_0(A_128))) | ~m1_subset_1(B_127, u1_struct_0(A_128)) | ~l1_pre_topc(A_128) | ~v2_pre_topc(A_128) | v2_struct_0(A_128))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.66/1.39  tff(c_355, plain, (![B_127]: (r2_hidden(B_127, k1_tops_1('#skF_1', '#skF_2')) | ~m1_connsp_2('#skF_2', '#skF_1', B_127) | ~m1_subset_1(B_127, u1_struct_0('#skF_1')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_26, c_350])).
% 2.66/1.39  tff(c_359, plain, (![B_127]: (r2_hidden(B_127, k1_tops_1('#skF_1', '#skF_2')) | ~m1_connsp_2('#skF_2', '#skF_1', B_127) | ~m1_subset_1(B_127, u1_struct_0('#skF_1')) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_355])).
% 2.66/1.39  tff(c_361, plain, (![B_130]: (r2_hidden(B_130, k1_tops_1('#skF_1', '#skF_2')) | ~m1_connsp_2('#skF_2', '#skF_1', B_130) | ~m1_subset_1(B_130, u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_32, c_359])).
% 2.66/1.39  tff(c_275, plain, (![C_91, B_92, A_93]: (~v1_xboole_0(C_91) | ~m1_subset_1(B_92, k1_zfmisc_1(C_91)) | ~r2_hidden(A_93, B_92))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.66/1.39  tff(c_280, plain, (![B_4, A_93, A_3]: (~v1_xboole_0(B_4) | ~r2_hidden(A_93, A_3) | ~r1_tarski(A_3, B_4))), inference(resolution, [status(thm)], [c_6, c_275])).
% 2.66/1.39  tff(c_373, plain, (![B_4, B_130]: (~v1_xboole_0(B_4) | ~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), B_4) | ~m1_connsp_2('#skF_2', '#skF_1', B_130) | ~m1_subset_1(B_130, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_361, c_280])).
% 2.66/1.39  tff(c_375, plain, (![B_131]: (~m1_connsp_2('#skF_2', '#skF_1', B_131) | ~m1_subset_1(B_131, u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_373])).
% 2.66/1.39  tff(c_381, plain, (~m1_connsp_2('#skF_2', '#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_24, c_375])).
% 2.66/1.39  tff(c_386, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_381])).
% 2.66/1.39  tff(c_398, plain, (![B_134]: (~v1_xboole_0(B_134) | ~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), B_134))), inference(splitRight, [status(thm)], [c_373])).
% 2.66/1.39  tff(c_402, plain, (~v1_xboole_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_315, c_398])).
% 2.66/1.39  tff(c_409, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_37, c_28, c_273, c_402])).
% 2.66/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.66/1.39  
% 2.66/1.39  Inference rules
% 2.66/1.39  ----------------------
% 2.66/1.39  #Ref     : 0
% 2.66/1.39  #Sup     : 73
% 2.66/1.39  #Fact    : 0
% 2.66/1.39  #Define  : 0
% 2.66/1.39  #Split   : 11
% 2.66/1.39  #Chain   : 0
% 2.66/1.39  #Close   : 0
% 2.66/1.39  
% 2.66/1.39  Ordering : KBO
% 2.66/1.39  
% 2.66/1.39  Simplification rules
% 2.66/1.39  ----------------------
% 2.66/1.39  #Subsume      : 10
% 2.66/1.39  #Demod        : 46
% 2.66/1.39  #Tautology    : 7
% 2.66/1.39  #SimpNegUnit  : 8
% 2.66/1.39  #BackRed      : 0
% 2.66/1.39  
% 2.66/1.39  #Partial instantiations: 0
% 2.66/1.39  #Strategies tried      : 1
% 2.66/1.39  
% 2.66/1.39  Timing (in seconds)
% 2.66/1.39  ----------------------
% 2.66/1.40  Preprocessing        : 0.30
% 2.66/1.40  Parsing              : 0.17
% 2.66/1.40  CNF conversion       : 0.02
% 2.66/1.40  Main loop            : 0.32
% 2.66/1.40  Inferencing          : 0.14
% 2.66/1.40  Reduction            : 0.08
% 2.66/1.40  Demodulation         : 0.06
% 2.66/1.40  BG Simplification    : 0.02
% 2.66/1.40  Subsumption          : 0.06
% 2.66/1.40  Abstraction          : 0.01
% 2.66/1.40  MUC search           : 0.00
% 2.66/1.40  Cooper               : 0.00
% 2.66/1.40  Total                : 0.66
% 2.66/1.40  Index Insertion      : 0.00
% 2.66/1.40  Index Deletion       : 0.00
% 2.66/1.40  Index Matching       : 0.00
% 2.66/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
