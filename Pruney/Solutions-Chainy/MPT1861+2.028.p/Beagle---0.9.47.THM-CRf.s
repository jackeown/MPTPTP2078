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
% DateTime   : Thu Dec  3 10:29:13 EST 2020

% Result     : Theorem 7.04s
% Output     : CNFRefutation 7.24s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 179 expanded)
%              Number of leaves         :   26 (  73 expanded)
%              Depth                    :   10
%              Number of atoms          :  121 ( 419 expanded)
%              Number of equality atoms :    7 (  31 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > l1_pre_topc > k2_enumset1 > k9_subset_1 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_50,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_79,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( ( v2_tex_2(B,A)
                    | v2_tex_2(C,A) )
                 => v2_tex_2(k9_subset_1(u1_struct_0(A),B,C),A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tex_2)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => m1_subset_1(k9_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).

tff(f_34,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_64,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( r1_tarski(C,B)
                  & v2_tex_2(B,A) )
               => v2_tex_2(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_tex_2)).

tff(c_495,plain,(
    ! [A_114,B_115] :
      ( r2_hidden('#skF_1'(A_114,B_115),A_114)
      | r1_tarski(A_114,B_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_500,plain,(
    ! [A_114] : r1_tarski(A_114,A_114) ),
    inference(resolution,[status(thm)],[c_495,c_4])).

tff(c_20,plain,(
    ! [A_18,B_19] :
      ( m1_subset_1(A_18,k1_zfmisc_1(B_19))
      | ~ r1_tarski(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_32,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_28,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_79,plain,(
    ! [A_49,B_50,C_51] :
      ( k9_subset_1(A_49,B_50,C_51) = k3_xboole_0(B_50,C_51)
      | ~ m1_subset_1(C_51,k1_zfmisc_1(A_49)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_87,plain,(
    ! [B_50] : k9_subset_1(u1_struct_0('#skF_2'),B_50,'#skF_4') = k3_xboole_0(B_50,'#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_79])).

tff(c_24,plain,(
    ~ v2_tex_2(k9_subset_1(u1_struct_0('#skF_2'),'#skF_3','#skF_4'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_89,plain,(
    ~ v2_tex_2(k3_xboole_0('#skF_3','#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_24])).

tff(c_26,plain,
    ( v2_tex_2('#skF_4','#skF_2')
    | v2_tex_2('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_34,plain,(
    v2_tex_2('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_30,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_132,plain,(
    ! [A_59,B_60,C_61] :
      ( m1_subset_1(k9_subset_1(A_59,B_60,C_61),k1_zfmisc_1(A_59))
      | ~ m1_subset_1(C_61,k1_zfmisc_1(A_59)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_146,plain,(
    ! [B_50] :
      ( m1_subset_1(k3_xboole_0(B_50,'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_132])).

tff(c_152,plain,(
    ! [B_50] : m1_subset_1(k3_xboole_0(B_50,'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_146])).

tff(c_8,plain,(
    ! [A_6,B_7] : r1_tarski(k3_xboole_0(A_6,B_7),A_6) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_161,plain,(
    ! [C_63,A_64,B_65] :
      ( v2_tex_2(C_63,A_64)
      | ~ v2_tex_2(B_65,A_64)
      | ~ r1_tarski(C_63,B_65)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(u1_struct_0(A_64)))
      | ~ m1_subset_1(B_65,k1_zfmisc_1(u1_struct_0(A_64)))
      | ~ l1_pre_topc(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_383,plain,(
    ! [A_99,B_100,A_101] :
      ( v2_tex_2(k3_xboole_0(A_99,B_100),A_101)
      | ~ v2_tex_2(A_99,A_101)
      | ~ m1_subset_1(k3_xboole_0(A_99,B_100),k1_zfmisc_1(u1_struct_0(A_101)))
      | ~ m1_subset_1(A_99,k1_zfmisc_1(u1_struct_0(A_101)))
      | ~ l1_pre_topc(A_101) ) ),
    inference(resolution,[status(thm)],[c_8,c_161])).

tff(c_396,plain,(
    ! [B_50] :
      ( v2_tex_2(k3_xboole_0(B_50,'#skF_4'),'#skF_2')
      | ~ v2_tex_2(B_50,'#skF_2')
      | ~ m1_subset_1(B_50,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_152,c_383])).

tff(c_425,plain,(
    ! [B_105] :
      ( v2_tex_2(k3_xboole_0(B_105,'#skF_4'),'#skF_2')
      | ~ v2_tex_2(B_105,'#skF_2')
      | ~ m1_subset_1(B_105,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_396])).

tff(c_455,plain,
    ( v2_tex_2(k3_xboole_0('#skF_3','#skF_4'),'#skF_2')
    | ~ v2_tex_2('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_425])).

tff(c_466,plain,(
    v2_tex_2(k3_xboole_0('#skF_3','#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_455])).

tff(c_468,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_89,c_466])).

tff(c_469,plain,(
    v2_tex_2('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_515,plain,(
    ! [A_122,B_123,C_124] :
      ( k9_subset_1(A_122,B_123,C_124) = k3_xboole_0(B_123,C_124)
      | ~ m1_subset_1(C_124,k1_zfmisc_1(A_122)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_523,plain,(
    ! [B_123] : k9_subset_1(u1_struct_0('#skF_2'),B_123,'#skF_4') = k3_xboole_0(B_123,'#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_515])).

tff(c_535,plain,(
    ! [A_126,B_127,C_128] :
      ( m1_subset_1(k9_subset_1(A_126,B_127,C_128),k1_zfmisc_1(A_126))
      | ~ m1_subset_1(C_128,k1_zfmisc_1(A_126)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_543,plain,(
    ! [B_123] :
      ( m1_subset_1(k3_xboole_0(B_123,'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_523,c_535])).

tff(c_547,plain,(
    ! [B_123] : m1_subset_1(k3_xboole_0(B_123,'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_543])).

tff(c_580,plain,(
    ! [B_134,B_135,A_136] :
      ( k9_subset_1(B_134,B_135,A_136) = k3_xboole_0(B_135,A_136)
      | ~ r1_tarski(A_136,B_134) ) ),
    inference(resolution,[status(thm)],[c_20,c_515])).

tff(c_595,plain,(
    ! [A_114,B_135] : k9_subset_1(A_114,B_135,A_114) = k3_xboole_0(B_135,A_114) ),
    inference(resolution,[status(thm)],[c_500,c_580])).

tff(c_18,plain,(
    ! [A_18,B_19] :
      ( r1_tarski(A_18,B_19)
      | ~ m1_subset_1(A_18,k1_zfmisc_1(B_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_545,plain,(
    ! [A_126,B_127,C_128] :
      ( r1_tarski(k9_subset_1(A_126,B_127,C_128),A_126)
      | ~ m1_subset_1(C_128,k1_zfmisc_1(A_126)) ) ),
    inference(resolution,[status(thm)],[c_535,c_18])).

tff(c_634,plain,(
    ! [C_144,A_145,B_146] :
      ( v2_tex_2(C_144,A_145)
      | ~ v2_tex_2(B_146,A_145)
      | ~ r1_tarski(C_144,B_146)
      | ~ m1_subset_1(C_144,k1_zfmisc_1(u1_struct_0(A_145)))
      | ~ m1_subset_1(B_146,k1_zfmisc_1(u1_struct_0(A_145)))
      | ~ l1_pre_topc(A_145) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1936,plain,(
    ! [A_270,B_271,C_272,A_273] :
      ( v2_tex_2(k9_subset_1(A_270,B_271,C_272),A_273)
      | ~ v2_tex_2(A_270,A_273)
      | ~ m1_subset_1(k9_subset_1(A_270,B_271,C_272),k1_zfmisc_1(u1_struct_0(A_273)))
      | ~ m1_subset_1(A_270,k1_zfmisc_1(u1_struct_0(A_273)))
      | ~ l1_pre_topc(A_273)
      | ~ m1_subset_1(C_272,k1_zfmisc_1(A_270)) ) ),
    inference(resolution,[status(thm)],[c_545,c_634])).

tff(c_1966,plain,(
    ! [A_114,B_135,A_273] :
      ( v2_tex_2(k9_subset_1(A_114,B_135,A_114),A_273)
      | ~ v2_tex_2(A_114,A_273)
      | ~ m1_subset_1(k3_xboole_0(B_135,A_114),k1_zfmisc_1(u1_struct_0(A_273)))
      | ~ m1_subset_1(A_114,k1_zfmisc_1(u1_struct_0(A_273)))
      | ~ l1_pre_topc(A_273)
      | ~ m1_subset_1(A_114,k1_zfmisc_1(A_114)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_595,c_1936])).

tff(c_6271,plain,(
    ! [B_582,A_583,A_584] :
      ( v2_tex_2(k3_xboole_0(B_582,A_583),A_584)
      | ~ v2_tex_2(A_583,A_584)
      | ~ m1_subset_1(k3_xboole_0(B_582,A_583),k1_zfmisc_1(u1_struct_0(A_584)))
      | ~ m1_subset_1(A_583,k1_zfmisc_1(u1_struct_0(A_584)))
      | ~ l1_pre_topc(A_584)
      | ~ m1_subset_1(A_583,k1_zfmisc_1(A_583)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_595,c_1966])).

tff(c_6312,plain,(
    ! [B_123] :
      ( v2_tex_2(k3_xboole_0(B_123,'#skF_4'),'#skF_2')
      | ~ v2_tex_2('#skF_4','#skF_2')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_547,c_6271])).

tff(c_6352,plain,(
    ! [B_123] :
      ( v2_tex_2(k3_xboole_0(B_123,'#skF_4'),'#skF_2')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_28,c_469,c_6312])).

tff(c_6354,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_6352])).

tff(c_6357,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_20,c_6354])).

tff(c_6361,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_500,c_6357])).

tff(c_6362,plain,(
    ! [B_123] : v2_tex_2(k3_xboole_0(B_123,'#skF_4'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_6352])).

tff(c_525,plain,(
    ~ v2_tex_2(k3_xboole_0('#skF_3','#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_523,c_24])).

tff(c_6483,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6362,c_525])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:12:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.04/2.59  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.04/2.59  
% 7.04/2.59  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.04/2.59  %$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > l1_pre_topc > k2_enumset1 > k9_subset_1 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 7.04/2.59  
% 7.04/2.59  %Foreground sorts:
% 7.04/2.59  
% 7.04/2.59  
% 7.04/2.59  %Background operators:
% 7.04/2.59  
% 7.04/2.59  
% 7.04/2.59  %Foreground operators:
% 7.04/2.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.04/2.59  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.04/2.59  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 7.04/2.59  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.04/2.59  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 7.04/2.59  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.04/2.59  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 7.04/2.59  tff('#skF_2', type, '#skF_2': $i).
% 7.04/2.59  tff('#skF_3', type, '#skF_3': $i).
% 7.04/2.59  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.04/2.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.04/2.59  tff('#skF_4', type, '#skF_4': $i).
% 7.04/2.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.04/2.59  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.04/2.59  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 7.04/2.59  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 7.04/2.59  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 7.04/2.59  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.04/2.59  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 7.04/2.59  
% 7.24/2.61  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 7.24/2.61  tff(f_50, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 7.24/2.61  tff(f_79, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(B, A) | v2_tex_2(C, A)) => v2_tex_2(k9_subset_1(u1_struct_0(A), B, C), A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_tex_2)).
% 7.24/2.61  tff(f_44, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 7.24/2.61  tff(f_40, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => m1_subset_1(k9_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 7.24/2.61  tff(f_34, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 7.24/2.61  tff(f_64, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r1_tarski(C, B) & v2_tex_2(B, A)) => v2_tex_2(C, A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_tex_2)).
% 7.24/2.61  tff(c_495, plain, (![A_114, B_115]: (r2_hidden('#skF_1'(A_114, B_115), A_114) | r1_tarski(A_114, B_115))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.24/2.61  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.24/2.61  tff(c_500, plain, (![A_114]: (r1_tarski(A_114, A_114))), inference(resolution, [status(thm)], [c_495, c_4])).
% 7.24/2.61  tff(c_20, plain, (![A_18, B_19]: (m1_subset_1(A_18, k1_zfmisc_1(B_19)) | ~r1_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_50])).
% 7.24/2.61  tff(c_32, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_79])).
% 7.24/2.61  tff(c_28, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_79])).
% 7.24/2.61  tff(c_79, plain, (![A_49, B_50, C_51]: (k9_subset_1(A_49, B_50, C_51)=k3_xboole_0(B_50, C_51) | ~m1_subset_1(C_51, k1_zfmisc_1(A_49)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 7.24/2.61  tff(c_87, plain, (![B_50]: (k9_subset_1(u1_struct_0('#skF_2'), B_50, '#skF_4')=k3_xboole_0(B_50, '#skF_4'))), inference(resolution, [status(thm)], [c_28, c_79])).
% 7.24/2.61  tff(c_24, plain, (~v2_tex_2(k9_subset_1(u1_struct_0('#skF_2'), '#skF_3', '#skF_4'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_79])).
% 7.24/2.61  tff(c_89, plain, (~v2_tex_2(k3_xboole_0('#skF_3', '#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_87, c_24])).
% 7.24/2.61  tff(c_26, plain, (v2_tex_2('#skF_4', '#skF_2') | v2_tex_2('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_79])).
% 7.24/2.61  tff(c_34, plain, (v2_tex_2('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_26])).
% 7.24/2.61  tff(c_30, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_79])).
% 7.24/2.61  tff(c_132, plain, (![A_59, B_60, C_61]: (m1_subset_1(k9_subset_1(A_59, B_60, C_61), k1_zfmisc_1(A_59)) | ~m1_subset_1(C_61, k1_zfmisc_1(A_59)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 7.24/2.61  tff(c_146, plain, (![B_50]: (m1_subset_1(k3_xboole_0(B_50, '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(superposition, [status(thm), theory('equality')], [c_87, c_132])).
% 7.24/2.61  tff(c_152, plain, (![B_50]: (m1_subset_1(k3_xboole_0(B_50, '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_146])).
% 7.24/2.61  tff(c_8, plain, (![A_6, B_7]: (r1_tarski(k3_xboole_0(A_6, B_7), A_6))), inference(cnfTransformation, [status(thm)], [f_34])).
% 7.24/2.61  tff(c_161, plain, (![C_63, A_64, B_65]: (v2_tex_2(C_63, A_64) | ~v2_tex_2(B_65, A_64) | ~r1_tarski(C_63, B_65) | ~m1_subset_1(C_63, k1_zfmisc_1(u1_struct_0(A_64))) | ~m1_subset_1(B_65, k1_zfmisc_1(u1_struct_0(A_64))) | ~l1_pre_topc(A_64))), inference(cnfTransformation, [status(thm)], [f_64])).
% 7.24/2.61  tff(c_383, plain, (![A_99, B_100, A_101]: (v2_tex_2(k3_xboole_0(A_99, B_100), A_101) | ~v2_tex_2(A_99, A_101) | ~m1_subset_1(k3_xboole_0(A_99, B_100), k1_zfmisc_1(u1_struct_0(A_101))) | ~m1_subset_1(A_99, k1_zfmisc_1(u1_struct_0(A_101))) | ~l1_pre_topc(A_101))), inference(resolution, [status(thm)], [c_8, c_161])).
% 7.24/2.61  tff(c_396, plain, (![B_50]: (v2_tex_2(k3_xboole_0(B_50, '#skF_4'), '#skF_2') | ~v2_tex_2(B_50, '#skF_2') | ~m1_subset_1(B_50, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_152, c_383])).
% 7.24/2.61  tff(c_425, plain, (![B_105]: (v2_tex_2(k3_xboole_0(B_105, '#skF_4'), '#skF_2') | ~v2_tex_2(B_105, '#skF_2') | ~m1_subset_1(B_105, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_396])).
% 7.24/2.61  tff(c_455, plain, (v2_tex_2(k3_xboole_0('#skF_3', '#skF_4'), '#skF_2') | ~v2_tex_2('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_30, c_425])).
% 7.24/2.61  tff(c_466, plain, (v2_tex_2(k3_xboole_0('#skF_3', '#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_455])).
% 7.24/2.61  tff(c_468, plain, $false, inference(negUnitSimplification, [status(thm)], [c_89, c_466])).
% 7.24/2.61  tff(c_469, plain, (v2_tex_2('#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_26])).
% 7.24/2.61  tff(c_515, plain, (![A_122, B_123, C_124]: (k9_subset_1(A_122, B_123, C_124)=k3_xboole_0(B_123, C_124) | ~m1_subset_1(C_124, k1_zfmisc_1(A_122)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 7.24/2.61  tff(c_523, plain, (![B_123]: (k9_subset_1(u1_struct_0('#skF_2'), B_123, '#skF_4')=k3_xboole_0(B_123, '#skF_4'))), inference(resolution, [status(thm)], [c_28, c_515])).
% 7.24/2.61  tff(c_535, plain, (![A_126, B_127, C_128]: (m1_subset_1(k9_subset_1(A_126, B_127, C_128), k1_zfmisc_1(A_126)) | ~m1_subset_1(C_128, k1_zfmisc_1(A_126)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 7.24/2.61  tff(c_543, plain, (![B_123]: (m1_subset_1(k3_xboole_0(B_123, '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(superposition, [status(thm), theory('equality')], [c_523, c_535])).
% 7.24/2.61  tff(c_547, plain, (![B_123]: (m1_subset_1(k3_xboole_0(B_123, '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_543])).
% 7.24/2.61  tff(c_580, plain, (![B_134, B_135, A_136]: (k9_subset_1(B_134, B_135, A_136)=k3_xboole_0(B_135, A_136) | ~r1_tarski(A_136, B_134))), inference(resolution, [status(thm)], [c_20, c_515])).
% 7.24/2.61  tff(c_595, plain, (![A_114, B_135]: (k9_subset_1(A_114, B_135, A_114)=k3_xboole_0(B_135, A_114))), inference(resolution, [status(thm)], [c_500, c_580])).
% 7.24/2.61  tff(c_18, plain, (![A_18, B_19]: (r1_tarski(A_18, B_19) | ~m1_subset_1(A_18, k1_zfmisc_1(B_19)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 7.24/2.61  tff(c_545, plain, (![A_126, B_127, C_128]: (r1_tarski(k9_subset_1(A_126, B_127, C_128), A_126) | ~m1_subset_1(C_128, k1_zfmisc_1(A_126)))), inference(resolution, [status(thm)], [c_535, c_18])).
% 7.24/2.61  tff(c_634, plain, (![C_144, A_145, B_146]: (v2_tex_2(C_144, A_145) | ~v2_tex_2(B_146, A_145) | ~r1_tarski(C_144, B_146) | ~m1_subset_1(C_144, k1_zfmisc_1(u1_struct_0(A_145))) | ~m1_subset_1(B_146, k1_zfmisc_1(u1_struct_0(A_145))) | ~l1_pre_topc(A_145))), inference(cnfTransformation, [status(thm)], [f_64])).
% 7.24/2.61  tff(c_1936, plain, (![A_270, B_271, C_272, A_273]: (v2_tex_2(k9_subset_1(A_270, B_271, C_272), A_273) | ~v2_tex_2(A_270, A_273) | ~m1_subset_1(k9_subset_1(A_270, B_271, C_272), k1_zfmisc_1(u1_struct_0(A_273))) | ~m1_subset_1(A_270, k1_zfmisc_1(u1_struct_0(A_273))) | ~l1_pre_topc(A_273) | ~m1_subset_1(C_272, k1_zfmisc_1(A_270)))), inference(resolution, [status(thm)], [c_545, c_634])).
% 7.24/2.61  tff(c_1966, plain, (![A_114, B_135, A_273]: (v2_tex_2(k9_subset_1(A_114, B_135, A_114), A_273) | ~v2_tex_2(A_114, A_273) | ~m1_subset_1(k3_xboole_0(B_135, A_114), k1_zfmisc_1(u1_struct_0(A_273))) | ~m1_subset_1(A_114, k1_zfmisc_1(u1_struct_0(A_273))) | ~l1_pre_topc(A_273) | ~m1_subset_1(A_114, k1_zfmisc_1(A_114)))), inference(superposition, [status(thm), theory('equality')], [c_595, c_1936])).
% 7.24/2.61  tff(c_6271, plain, (![B_582, A_583, A_584]: (v2_tex_2(k3_xboole_0(B_582, A_583), A_584) | ~v2_tex_2(A_583, A_584) | ~m1_subset_1(k3_xboole_0(B_582, A_583), k1_zfmisc_1(u1_struct_0(A_584))) | ~m1_subset_1(A_583, k1_zfmisc_1(u1_struct_0(A_584))) | ~l1_pre_topc(A_584) | ~m1_subset_1(A_583, k1_zfmisc_1(A_583)))), inference(demodulation, [status(thm), theory('equality')], [c_595, c_1966])).
% 7.24/2.61  tff(c_6312, plain, (![B_123]: (v2_tex_2(k3_xboole_0(B_123, '#skF_4'), '#skF_2') | ~v2_tex_2('#skF_4', '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4')))), inference(resolution, [status(thm)], [c_547, c_6271])).
% 7.24/2.61  tff(c_6352, plain, (![B_123]: (v2_tex_2(k3_xboole_0(B_123, '#skF_4'), '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_28, c_469, c_6312])).
% 7.24/2.61  tff(c_6354, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_6352])).
% 7.24/2.61  tff(c_6357, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_20, c_6354])).
% 7.24/2.61  tff(c_6361, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_500, c_6357])).
% 7.24/2.61  tff(c_6362, plain, (![B_123]: (v2_tex_2(k3_xboole_0(B_123, '#skF_4'), '#skF_2'))), inference(splitRight, [status(thm)], [c_6352])).
% 7.24/2.61  tff(c_525, plain, (~v2_tex_2(k3_xboole_0('#skF_3', '#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_523, c_24])).
% 7.24/2.61  tff(c_6483, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6362, c_525])).
% 7.24/2.61  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.24/2.61  
% 7.24/2.61  Inference rules
% 7.24/2.61  ----------------------
% 7.24/2.61  #Ref     : 0
% 7.24/2.61  #Sup     : 1542
% 7.24/2.61  #Fact    : 0
% 7.24/2.61  #Define  : 0
% 7.24/2.61  #Split   : 6
% 7.24/2.61  #Chain   : 0
% 7.24/2.61  #Close   : 0
% 7.24/2.61  
% 7.24/2.61  Ordering : KBO
% 7.24/2.61  
% 7.24/2.61  Simplification rules
% 7.24/2.61  ----------------------
% 7.24/2.61  #Subsume      : 208
% 7.24/2.61  #Demod        : 510
% 7.24/2.61  #Tautology    : 385
% 7.24/2.61  #SimpNegUnit  : 6
% 7.24/2.61  #BackRed      : 4
% 7.24/2.61  
% 7.24/2.61  #Partial instantiations: 0
% 7.24/2.61  #Strategies tried      : 1
% 7.24/2.61  
% 7.24/2.61  Timing (in seconds)
% 7.24/2.61  ----------------------
% 7.24/2.61  Preprocessing        : 0.31
% 7.24/2.61  Parsing              : 0.17
% 7.24/2.61  CNF conversion       : 0.02
% 7.24/2.61  Main loop            : 1.54
% 7.24/2.61  Inferencing          : 0.51
% 7.24/2.61  Reduction            : 0.49
% 7.24/2.61  Demodulation         : 0.36
% 7.24/2.61  BG Simplification    : 0.06
% 7.24/2.61  Subsumption          : 0.37
% 7.24/2.61  Abstraction          : 0.08
% 7.24/2.61  MUC search           : 0.00
% 7.24/2.61  Cooper               : 0.00
% 7.24/2.61  Total                : 1.88
% 7.24/2.61  Index Insertion      : 0.00
% 7.24/2.61  Index Deletion       : 0.00
% 7.24/2.61  Index Matching       : 0.00
% 7.24/2.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
