%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:12 EST 2020

% Result     : Theorem 9.75s
% Output     : CNFRefutation 9.75s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 164 expanded)
%              Number of leaves         :   23 (  66 expanded)
%              Depth                    :   10
%              Number of atoms          :  135 ( 372 expanded)
%              Number of equality atoms :   16 (  50 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tex_2 > r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_76,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( ( v2_tex_2(B,A)
                    | v2_tex_2(C,A) )
                 => v2_tex_2(k9_subset_1(u1_struct_0(A),B,C),A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_tex_2)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k9_subset_1(A,C,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_61,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( r1_tarski(C,B)
                  & v2_tex_2(B,A) )
               => v2_tex_2(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_tex_2)).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k3_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_22,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_70,plain,(
    ! [A_40,B_41,C_42] :
      ( k9_subset_1(A_40,B_41,C_42) = k3_xboole_0(B_41,C_42)
      | ~ m1_subset_1(C_42,k1_zfmisc_1(A_40)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_78,plain,(
    ! [B_41] : k9_subset_1(u1_struct_0('#skF_1'),B_41,'#skF_3') = k3_xboole_0(B_41,'#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_70])).

tff(c_181,plain,(
    ! [A_62,C_63,B_64] :
      ( k9_subset_1(A_62,C_63,B_64) = k9_subset_1(A_62,B_64,C_63)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(A_62)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_185,plain,(
    ! [B_64] : k9_subset_1(u1_struct_0('#skF_1'),B_64,'#skF_3') = k9_subset_1(u1_struct_0('#skF_1'),'#skF_3',B_64) ),
    inference(resolution,[status(thm)],[c_22,c_181])).

tff(c_193,plain,(
    ! [B_65] : k9_subset_1(u1_struct_0('#skF_1'),'#skF_3',B_65) = k3_xboole_0(B_65,'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_185])).

tff(c_24,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_79,plain,(
    ! [B_41] : k9_subset_1(u1_struct_0('#skF_1'),B_41,'#skF_2') = k3_xboole_0(B_41,'#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_70])).

tff(c_204,plain,(
    k3_xboole_0('#skF_2','#skF_3') = k3_xboole_0('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_193,c_79])).

tff(c_18,plain,(
    ~ v2_tex_2(k9_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_104,plain,(
    ~ v2_tex_2(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_18])).

tff(c_220,plain,(
    ~ v2_tex_2(k3_xboole_0('#skF_3','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_204,c_104])).

tff(c_20,plain,
    ( v2_tex_2('#skF_3','#skF_1')
    | v2_tex_2('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_28,plain,(
    v2_tex_2('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_20])).

tff(c_26,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_30,plain,(
    ! [A_31,B_32] :
      ( r1_tarski(A_31,B_32)
      | ~ m1_subset_1(A_31,k1_zfmisc_1(B_32)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_41,plain,(
    r1_tarski('#skF_3',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_22,c_30])).

tff(c_52,plain,(
    ! [A_35,C_36,B_37] :
      ( r1_tarski(A_35,C_36)
      | ~ r1_tarski(B_37,C_36)
      | ~ r1_tarski(A_35,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_60,plain,(
    ! [A_35] :
      ( r1_tarski(A_35,u1_struct_0('#skF_1'))
      | ~ r1_tarski(A_35,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_41,c_52])).

tff(c_14,plain,(
    ! [A_14,B_15] :
      ( m1_subset_1(A_14,k1_zfmisc_1(B_15))
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_306,plain,(
    ! [C_69,A_70,B_71] :
      ( v2_tex_2(C_69,A_70)
      | ~ v2_tex_2(B_71,A_70)
      | ~ r1_tarski(C_69,B_71)
      | ~ m1_subset_1(C_69,k1_zfmisc_1(u1_struct_0(A_70)))
      | ~ m1_subset_1(B_71,k1_zfmisc_1(u1_struct_0(A_70)))
      | ~ l1_pre_topc(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_628,plain,(
    ! [A_96,B_97,A_98] :
      ( v2_tex_2(k3_xboole_0(A_96,B_97),A_98)
      | ~ v2_tex_2(A_96,A_98)
      | ~ m1_subset_1(k3_xboole_0(A_96,B_97),k1_zfmisc_1(u1_struct_0(A_98)))
      | ~ m1_subset_1(A_96,k1_zfmisc_1(u1_struct_0(A_98)))
      | ~ l1_pre_topc(A_98) ) ),
    inference(resolution,[status(thm)],[c_2,c_306])).

tff(c_1130,plain,(
    ! [A_115,B_116,A_117] :
      ( v2_tex_2(k3_xboole_0(A_115,B_116),A_117)
      | ~ v2_tex_2(A_115,A_117)
      | ~ m1_subset_1(A_115,k1_zfmisc_1(u1_struct_0(A_117)))
      | ~ l1_pre_topc(A_117)
      | ~ r1_tarski(k3_xboole_0(A_115,B_116),u1_struct_0(A_117)) ) ),
    inference(resolution,[status(thm)],[c_14,c_628])).

tff(c_1166,plain,(
    ! [A_115,B_116] :
      ( v2_tex_2(k3_xboole_0(A_115,B_116),'#skF_1')
      | ~ v2_tex_2(A_115,'#skF_1')
      | ~ m1_subset_1(A_115,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ r1_tarski(k3_xboole_0(A_115,B_116),'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_60,c_1130])).

tff(c_6376,plain,(
    ! [A_262,B_263] :
      ( v2_tex_2(k3_xboole_0(A_262,B_263),'#skF_1')
      | ~ v2_tex_2(A_262,'#skF_1')
      | ~ m1_subset_1(A_262,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ r1_tarski(k3_xboole_0(A_262,B_263),'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_1166])).

tff(c_6383,plain,(
    ! [B_263] :
      ( v2_tex_2(k3_xboole_0('#skF_2',B_263),'#skF_1')
      | ~ v2_tex_2('#skF_2','#skF_1')
      | ~ r1_tarski(k3_xboole_0('#skF_2',B_263),'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_24,c_6376])).

tff(c_6391,plain,(
    ! [B_264] :
      ( v2_tex_2(k3_xboole_0('#skF_2',B_264),'#skF_1')
      | ~ r1_tarski(k3_xboole_0('#skF_2',B_264),'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_6383])).

tff(c_6394,plain,
    ( v2_tex_2(k3_xboole_0('#skF_3','#skF_2'),'#skF_1')
    | ~ r1_tarski(k3_xboole_0('#skF_2','#skF_3'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_204,c_6391])).

tff(c_6396,plain,(
    v2_tex_2(k3_xboole_0('#skF_3','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_204,c_6394])).

tff(c_6398,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_220,c_6396])).

tff(c_6399,plain,(
    v2_tex_2('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_20])).

tff(c_6411,plain,(
    ! [A_269,B_270] :
      ( r1_tarski(A_269,B_270)
      | ~ m1_subset_1(A_269,k1_zfmisc_1(B_270)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_6422,plain,(
    r1_tarski('#skF_3',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_22,c_6411])).

tff(c_6424,plain,(
    ! [A_271,C_272,B_273] :
      ( r1_tarski(A_271,C_272)
      | ~ r1_tarski(B_273,C_272)
      | ~ r1_tarski(A_271,B_273) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_6432,plain,(
    ! [A_271] :
      ( r1_tarski(A_271,u1_struct_0('#skF_1'))
      | ~ r1_tarski(A_271,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_6422,c_6424])).

tff(c_6902,plain,(
    ! [C_323,A_324,B_325] :
      ( v2_tex_2(C_323,A_324)
      | ~ v2_tex_2(B_325,A_324)
      | ~ r1_tarski(C_323,B_325)
      | ~ m1_subset_1(C_323,k1_zfmisc_1(u1_struct_0(A_324)))
      | ~ m1_subset_1(B_325,k1_zfmisc_1(u1_struct_0(A_324)))
      | ~ l1_pre_topc(A_324) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_7099,plain,(
    ! [A_337,B_338,A_339] :
      ( v2_tex_2(k3_xboole_0(A_337,B_338),A_339)
      | ~ v2_tex_2(A_337,A_339)
      | ~ m1_subset_1(k3_xboole_0(A_337,B_338),k1_zfmisc_1(u1_struct_0(A_339)))
      | ~ m1_subset_1(A_337,k1_zfmisc_1(u1_struct_0(A_339)))
      | ~ l1_pre_topc(A_339) ) ),
    inference(resolution,[status(thm)],[c_2,c_6902])).

tff(c_7703,plain,(
    ! [A_351,B_352,A_353] :
      ( v2_tex_2(k3_xboole_0(A_351,B_352),A_353)
      | ~ v2_tex_2(A_351,A_353)
      | ~ m1_subset_1(A_351,k1_zfmisc_1(u1_struct_0(A_353)))
      | ~ l1_pre_topc(A_353)
      | ~ r1_tarski(k3_xboole_0(A_351,B_352),u1_struct_0(A_353)) ) ),
    inference(resolution,[status(thm)],[c_14,c_7099])).

tff(c_7751,plain,(
    ! [A_351,B_352] :
      ( v2_tex_2(k3_xboole_0(A_351,B_352),'#skF_1')
      | ~ v2_tex_2(A_351,'#skF_1')
      | ~ m1_subset_1(A_351,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ r1_tarski(k3_xboole_0(A_351,B_352),'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_6432,c_7703])).

tff(c_12668,plain,(
    ! [A_489,B_490] :
      ( v2_tex_2(k3_xboole_0(A_489,B_490),'#skF_1')
      | ~ v2_tex_2(A_489,'#skF_1')
      | ~ m1_subset_1(A_489,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ r1_tarski(k3_xboole_0(A_489,B_490),'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_7751])).

tff(c_12673,plain,(
    ! [B_490] :
      ( v2_tex_2(k3_xboole_0('#skF_3',B_490),'#skF_1')
      | ~ v2_tex_2('#skF_3','#skF_1')
      | ~ r1_tarski(k3_xboole_0('#skF_3',B_490),'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_22,c_12668])).

tff(c_12679,plain,(
    ! [B_490] : v2_tex_2(k3_xboole_0('#skF_3',B_490),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_6399,c_12673])).

tff(c_6534,plain,(
    ! [A_294,B_295,C_296] :
      ( k9_subset_1(A_294,B_295,C_296) = k3_xboole_0(B_295,C_296)
      | ~ m1_subset_1(C_296,k1_zfmisc_1(A_294)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_6542,plain,(
    ! [B_295] : k9_subset_1(u1_struct_0('#skF_1'),B_295,'#skF_3') = k3_xboole_0(B_295,'#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_6534])).

tff(c_6714,plain,(
    ! [A_316,C_317,B_318] :
      ( k9_subset_1(A_316,C_317,B_318) = k9_subset_1(A_316,B_318,C_317)
      | ~ m1_subset_1(C_317,k1_zfmisc_1(A_316)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_6718,plain,(
    ! [B_318] : k9_subset_1(u1_struct_0('#skF_1'),B_318,'#skF_3') = k9_subset_1(u1_struct_0('#skF_1'),'#skF_3',B_318) ),
    inference(resolution,[status(thm)],[c_22,c_6714])).

tff(c_6726,plain,(
    ! [B_319] : k9_subset_1(u1_struct_0('#skF_1'),'#skF_3',B_319) = k3_xboole_0(B_319,'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6542,c_6718])).

tff(c_6543,plain,(
    ! [B_295] : k9_subset_1(u1_struct_0('#skF_1'),B_295,'#skF_2') = k3_xboole_0(B_295,'#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_6534])).

tff(c_6743,plain,(
    k3_xboole_0('#skF_2','#skF_3') = k3_xboole_0('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_6726,c_6543])).

tff(c_6544,plain,(
    ~ v2_tex_2(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6542,c_18])).

tff(c_6775,plain,(
    ~ v2_tex_2(k3_xboole_0('#skF_3','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6743,c_6544])).

tff(c_12686,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12679,c_6775])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:36:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.75/3.32  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.75/3.32  
% 9.75/3.32  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.75/3.32  %$ v2_tex_2 > r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 9.75/3.32  
% 9.75/3.32  %Foreground sorts:
% 9.75/3.32  
% 9.75/3.32  
% 9.75/3.32  %Background operators:
% 9.75/3.32  
% 9.75/3.32  
% 9.75/3.32  %Foreground operators:
% 9.75/3.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.75/3.32  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 9.75/3.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.75/3.32  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 9.75/3.32  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 9.75/3.32  tff('#skF_2', type, '#skF_2': $i).
% 9.75/3.32  tff('#skF_3', type, '#skF_3': $i).
% 9.75/3.32  tff('#skF_1', type, '#skF_1': $i).
% 9.75/3.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.75/3.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.75/3.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.75/3.32  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 9.75/3.32  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 9.75/3.32  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 9.75/3.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.75/3.32  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 9.75/3.32  
% 9.75/3.34  tff(f_27, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 9.75/3.34  tff(f_76, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(B, A) | v2_tex_2(C, A)) => v2_tex_2(k9_subset_1(u1_struct_0(A), B, C), A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_tex_2)).
% 9.75/3.34  tff(f_41, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 9.75/3.34  tff(f_37, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k9_subset_1(A, C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k9_subset_1)).
% 9.75/3.34  tff(f_47, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 9.75/3.34  tff(f_33, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 9.75/3.34  tff(f_61, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r1_tarski(C, B) & v2_tex_2(B, A)) => v2_tex_2(C, A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_tex_2)).
% 9.75/3.34  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k3_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 9.75/3.34  tff(c_22, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_76])).
% 9.75/3.34  tff(c_70, plain, (![A_40, B_41, C_42]: (k9_subset_1(A_40, B_41, C_42)=k3_xboole_0(B_41, C_42) | ~m1_subset_1(C_42, k1_zfmisc_1(A_40)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 9.75/3.34  tff(c_78, plain, (![B_41]: (k9_subset_1(u1_struct_0('#skF_1'), B_41, '#skF_3')=k3_xboole_0(B_41, '#skF_3'))), inference(resolution, [status(thm)], [c_22, c_70])).
% 9.75/3.34  tff(c_181, plain, (![A_62, C_63, B_64]: (k9_subset_1(A_62, C_63, B_64)=k9_subset_1(A_62, B_64, C_63) | ~m1_subset_1(C_63, k1_zfmisc_1(A_62)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 9.75/3.34  tff(c_185, plain, (![B_64]: (k9_subset_1(u1_struct_0('#skF_1'), B_64, '#skF_3')=k9_subset_1(u1_struct_0('#skF_1'), '#skF_3', B_64))), inference(resolution, [status(thm)], [c_22, c_181])).
% 9.75/3.34  tff(c_193, plain, (![B_65]: (k9_subset_1(u1_struct_0('#skF_1'), '#skF_3', B_65)=k3_xboole_0(B_65, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_185])).
% 9.75/3.34  tff(c_24, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_76])).
% 9.75/3.34  tff(c_79, plain, (![B_41]: (k9_subset_1(u1_struct_0('#skF_1'), B_41, '#skF_2')=k3_xboole_0(B_41, '#skF_2'))), inference(resolution, [status(thm)], [c_24, c_70])).
% 9.75/3.34  tff(c_204, plain, (k3_xboole_0('#skF_2', '#skF_3')=k3_xboole_0('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_193, c_79])).
% 9.75/3.34  tff(c_18, plain, (~v2_tex_2(k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_76])).
% 9.75/3.34  tff(c_104, plain, (~v2_tex_2(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_18])).
% 9.75/3.34  tff(c_220, plain, (~v2_tex_2(k3_xboole_0('#skF_3', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_204, c_104])).
% 9.75/3.34  tff(c_20, plain, (v2_tex_2('#skF_3', '#skF_1') | v2_tex_2('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_76])).
% 9.75/3.34  tff(c_28, plain, (v2_tex_2('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_20])).
% 9.75/3.34  tff(c_26, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_76])).
% 9.75/3.34  tff(c_30, plain, (![A_31, B_32]: (r1_tarski(A_31, B_32) | ~m1_subset_1(A_31, k1_zfmisc_1(B_32)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 9.75/3.34  tff(c_41, plain, (r1_tarski('#skF_3', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_22, c_30])).
% 9.75/3.34  tff(c_52, plain, (![A_35, C_36, B_37]: (r1_tarski(A_35, C_36) | ~r1_tarski(B_37, C_36) | ~r1_tarski(A_35, B_37))), inference(cnfTransformation, [status(thm)], [f_33])).
% 9.75/3.34  tff(c_60, plain, (![A_35]: (r1_tarski(A_35, u1_struct_0('#skF_1')) | ~r1_tarski(A_35, '#skF_3'))), inference(resolution, [status(thm)], [c_41, c_52])).
% 9.75/3.34  tff(c_14, plain, (![A_14, B_15]: (m1_subset_1(A_14, k1_zfmisc_1(B_15)) | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_47])).
% 9.75/3.34  tff(c_306, plain, (![C_69, A_70, B_71]: (v2_tex_2(C_69, A_70) | ~v2_tex_2(B_71, A_70) | ~r1_tarski(C_69, B_71) | ~m1_subset_1(C_69, k1_zfmisc_1(u1_struct_0(A_70))) | ~m1_subset_1(B_71, k1_zfmisc_1(u1_struct_0(A_70))) | ~l1_pre_topc(A_70))), inference(cnfTransformation, [status(thm)], [f_61])).
% 9.75/3.34  tff(c_628, plain, (![A_96, B_97, A_98]: (v2_tex_2(k3_xboole_0(A_96, B_97), A_98) | ~v2_tex_2(A_96, A_98) | ~m1_subset_1(k3_xboole_0(A_96, B_97), k1_zfmisc_1(u1_struct_0(A_98))) | ~m1_subset_1(A_96, k1_zfmisc_1(u1_struct_0(A_98))) | ~l1_pre_topc(A_98))), inference(resolution, [status(thm)], [c_2, c_306])).
% 9.75/3.34  tff(c_1130, plain, (![A_115, B_116, A_117]: (v2_tex_2(k3_xboole_0(A_115, B_116), A_117) | ~v2_tex_2(A_115, A_117) | ~m1_subset_1(A_115, k1_zfmisc_1(u1_struct_0(A_117))) | ~l1_pre_topc(A_117) | ~r1_tarski(k3_xboole_0(A_115, B_116), u1_struct_0(A_117)))), inference(resolution, [status(thm)], [c_14, c_628])).
% 9.75/3.34  tff(c_1166, plain, (![A_115, B_116]: (v2_tex_2(k3_xboole_0(A_115, B_116), '#skF_1') | ~v2_tex_2(A_115, '#skF_1') | ~m1_subset_1(A_115, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~r1_tarski(k3_xboole_0(A_115, B_116), '#skF_3'))), inference(resolution, [status(thm)], [c_60, c_1130])).
% 9.75/3.34  tff(c_6376, plain, (![A_262, B_263]: (v2_tex_2(k3_xboole_0(A_262, B_263), '#skF_1') | ~v2_tex_2(A_262, '#skF_1') | ~m1_subset_1(A_262, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~r1_tarski(k3_xboole_0(A_262, B_263), '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_1166])).
% 9.75/3.34  tff(c_6383, plain, (![B_263]: (v2_tex_2(k3_xboole_0('#skF_2', B_263), '#skF_1') | ~v2_tex_2('#skF_2', '#skF_1') | ~r1_tarski(k3_xboole_0('#skF_2', B_263), '#skF_3'))), inference(resolution, [status(thm)], [c_24, c_6376])).
% 9.75/3.34  tff(c_6391, plain, (![B_264]: (v2_tex_2(k3_xboole_0('#skF_2', B_264), '#skF_1') | ~r1_tarski(k3_xboole_0('#skF_2', B_264), '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_6383])).
% 9.75/3.34  tff(c_6394, plain, (v2_tex_2(k3_xboole_0('#skF_3', '#skF_2'), '#skF_1') | ~r1_tarski(k3_xboole_0('#skF_2', '#skF_3'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_204, c_6391])).
% 9.75/3.34  tff(c_6396, plain, (v2_tex_2(k3_xboole_0('#skF_3', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_204, c_6394])).
% 9.75/3.34  tff(c_6398, plain, $false, inference(negUnitSimplification, [status(thm)], [c_220, c_6396])).
% 9.75/3.34  tff(c_6399, plain, (v2_tex_2('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_20])).
% 9.75/3.34  tff(c_6411, plain, (![A_269, B_270]: (r1_tarski(A_269, B_270) | ~m1_subset_1(A_269, k1_zfmisc_1(B_270)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 9.75/3.34  tff(c_6422, plain, (r1_tarski('#skF_3', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_22, c_6411])).
% 9.75/3.34  tff(c_6424, plain, (![A_271, C_272, B_273]: (r1_tarski(A_271, C_272) | ~r1_tarski(B_273, C_272) | ~r1_tarski(A_271, B_273))), inference(cnfTransformation, [status(thm)], [f_33])).
% 9.75/3.34  tff(c_6432, plain, (![A_271]: (r1_tarski(A_271, u1_struct_0('#skF_1')) | ~r1_tarski(A_271, '#skF_3'))), inference(resolution, [status(thm)], [c_6422, c_6424])).
% 9.75/3.34  tff(c_6902, plain, (![C_323, A_324, B_325]: (v2_tex_2(C_323, A_324) | ~v2_tex_2(B_325, A_324) | ~r1_tarski(C_323, B_325) | ~m1_subset_1(C_323, k1_zfmisc_1(u1_struct_0(A_324))) | ~m1_subset_1(B_325, k1_zfmisc_1(u1_struct_0(A_324))) | ~l1_pre_topc(A_324))), inference(cnfTransformation, [status(thm)], [f_61])).
% 9.75/3.34  tff(c_7099, plain, (![A_337, B_338, A_339]: (v2_tex_2(k3_xboole_0(A_337, B_338), A_339) | ~v2_tex_2(A_337, A_339) | ~m1_subset_1(k3_xboole_0(A_337, B_338), k1_zfmisc_1(u1_struct_0(A_339))) | ~m1_subset_1(A_337, k1_zfmisc_1(u1_struct_0(A_339))) | ~l1_pre_topc(A_339))), inference(resolution, [status(thm)], [c_2, c_6902])).
% 9.75/3.34  tff(c_7703, plain, (![A_351, B_352, A_353]: (v2_tex_2(k3_xboole_0(A_351, B_352), A_353) | ~v2_tex_2(A_351, A_353) | ~m1_subset_1(A_351, k1_zfmisc_1(u1_struct_0(A_353))) | ~l1_pre_topc(A_353) | ~r1_tarski(k3_xboole_0(A_351, B_352), u1_struct_0(A_353)))), inference(resolution, [status(thm)], [c_14, c_7099])).
% 9.75/3.34  tff(c_7751, plain, (![A_351, B_352]: (v2_tex_2(k3_xboole_0(A_351, B_352), '#skF_1') | ~v2_tex_2(A_351, '#skF_1') | ~m1_subset_1(A_351, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~r1_tarski(k3_xboole_0(A_351, B_352), '#skF_3'))), inference(resolution, [status(thm)], [c_6432, c_7703])).
% 9.75/3.34  tff(c_12668, plain, (![A_489, B_490]: (v2_tex_2(k3_xboole_0(A_489, B_490), '#skF_1') | ~v2_tex_2(A_489, '#skF_1') | ~m1_subset_1(A_489, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~r1_tarski(k3_xboole_0(A_489, B_490), '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_7751])).
% 9.75/3.34  tff(c_12673, plain, (![B_490]: (v2_tex_2(k3_xboole_0('#skF_3', B_490), '#skF_1') | ~v2_tex_2('#skF_3', '#skF_1') | ~r1_tarski(k3_xboole_0('#skF_3', B_490), '#skF_3'))), inference(resolution, [status(thm)], [c_22, c_12668])).
% 9.75/3.34  tff(c_12679, plain, (![B_490]: (v2_tex_2(k3_xboole_0('#skF_3', B_490), '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_6399, c_12673])).
% 9.75/3.34  tff(c_6534, plain, (![A_294, B_295, C_296]: (k9_subset_1(A_294, B_295, C_296)=k3_xboole_0(B_295, C_296) | ~m1_subset_1(C_296, k1_zfmisc_1(A_294)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 9.75/3.34  tff(c_6542, plain, (![B_295]: (k9_subset_1(u1_struct_0('#skF_1'), B_295, '#skF_3')=k3_xboole_0(B_295, '#skF_3'))), inference(resolution, [status(thm)], [c_22, c_6534])).
% 9.75/3.34  tff(c_6714, plain, (![A_316, C_317, B_318]: (k9_subset_1(A_316, C_317, B_318)=k9_subset_1(A_316, B_318, C_317) | ~m1_subset_1(C_317, k1_zfmisc_1(A_316)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 9.75/3.34  tff(c_6718, plain, (![B_318]: (k9_subset_1(u1_struct_0('#skF_1'), B_318, '#skF_3')=k9_subset_1(u1_struct_0('#skF_1'), '#skF_3', B_318))), inference(resolution, [status(thm)], [c_22, c_6714])).
% 9.75/3.34  tff(c_6726, plain, (![B_319]: (k9_subset_1(u1_struct_0('#skF_1'), '#skF_3', B_319)=k3_xboole_0(B_319, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_6542, c_6718])).
% 9.75/3.34  tff(c_6543, plain, (![B_295]: (k9_subset_1(u1_struct_0('#skF_1'), B_295, '#skF_2')=k3_xboole_0(B_295, '#skF_2'))), inference(resolution, [status(thm)], [c_24, c_6534])).
% 9.75/3.34  tff(c_6743, plain, (k3_xboole_0('#skF_2', '#skF_3')=k3_xboole_0('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_6726, c_6543])).
% 9.75/3.34  tff(c_6544, plain, (~v2_tex_2(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_6542, c_18])).
% 9.75/3.34  tff(c_6775, plain, (~v2_tex_2(k3_xboole_0('#skF_3', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_6743, c_6544])).
% 9.75/3.34  tff(c_12686, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12679, c_6775])).
% 9.75/3.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.75/3.34  
% 9.75/3.34  Inference rules
% 9.75/3.34  ----------------------
% 9.75/3.34  #Ref     : 0
% 9.75/3.34  #Sup     : 3136
% 9.75/3.34  #Fact    : 0
% 9.75/3.34  #Define  : 0
% 9.75/3.34  #Split   : 6
% 9.75/3.34  #Chain   : 0
% 9.75/3.34  #Close   : 0
% 9.75/3.34  
% 9.75/3.34  Ordering : KBO
% 9.75/3.34  
% 9.75/3.34  Simplification rules
% 9.75/3.34  ----------------------
% 9.75/3.34  #Subsume      : 191
% 9.75/3.34  #Demod        : 1402
% 9.75/3.34  #Tautology    : 1096
% 9.75/3.34  #SimpNegUnit  : 1
% 9.75/3.34  #BackRed      : 5
% 9.75/3.34  
% 9.75/3.34  #Partial instantiations: 0
% 9.75/3.34  #Strategies tried      : 1
% 9.75/3.34  
% 9.75/3.34  Timing (in seconds)
% 9.75/3.34  ----------------------
% 9.75/3.34  Preprocessing        : 0.30
% 9.75/3.34  Parsing              : 0.16
% 9.75/3.34  CNF conversion       : 0.02
% 9.75/3.34  Main loop            : 2.27
% 9.75/3.34  Inferencing          : 0.62
% 9.75/3.34  Reduction            : 0.97
% 9.75/3.34  Demodulation         : 0.78
% 9.75/3.34  BG Simplification    : 0.09
% 9.75/3.34  Subsumption          : 0.42
% 9.75/3.34  Abstraction          : 0.13
% 9.75/3.34  MUC search           : 0.00
% 9.75/3.34  Cooper               : 0.00
% 9.75/3.34  Total                : 2.60
% 9.75/3.34  Index Insertion      : 0.00
% 9.75/3.34  Index Deletion       : 0.00
% 9.75/3.34  Index Matching       : 0.00
% 9.75/3.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
