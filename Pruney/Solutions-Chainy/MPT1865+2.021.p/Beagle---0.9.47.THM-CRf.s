%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:20 EST 2020

% Result     : Theorem 6.90s
% Output     : CNFRefutation 6.90s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 133 expanded)
%              Number of leaves         :   28 (  62 expanded)
%              Depth                    :   13
%              Number of atoms          :  148 ( 396 expanded)
%              Number of equality atoms :   24 (  68 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > l1_pre_topc > k2_enumset1 > k9_subset_1 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_90,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v2_tex_2(B,A)
             => ! [C] :
                  ( m1_subset_1(C,u1_struct_0(A))
                 => ~ ( r2_hidden(C,B)
                      & ! [D] :
                          ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                         => ~ ( v4_pre_topc(D,A)
                              & k9_subset_1(u1_struct_0(A),B,D) = k1_tarski(C) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_tex_2)).

tff(f_31,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => m1_subset_1(k9_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).

tff(f_68,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tex_2(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ~ ( r1_tarski(C,B)
                    & ! [D] :
                        ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                       => ~ ( v4_pre_topc(D,A)
                            & k9_subset_1(u1_struct_0(A),B,D) = C ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_tex_2)).

tff(c_32,plain,(
    r2_hidden('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_4,plain,(
    ! [A_3] : k2_tarski(A_3,A_3) = k1_tarski(A_3) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_79,plain,(
    ! [A_69,B_70,C_71] :
      ( r1_tarski(k2_tarski(A_69,B_70),C_71)
      | ~ r2_hidden(B_70,C_71)
      | ~ r2_hidden(A_69,C_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_104,plain,(
    ! [A_73,C_74] :
      ( r1_tarski(k1_tarski(A_73),C_74)
      | ~ r2_hidden(A_73,C_74)
      | ~ r2_hidden(A_73,C_74) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_79])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = A_1
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_112,plain,(
    ! [A_73,C_74] :
      ( k3_xboole_0(k1_tarski(A_73),C_74) = k1_tarski(A_73)
      | ~ r2_hidden(A_73,C_74) ) ),
    inference(resolution,[status(thm)],[c_104,c_2])).

tff(c_91,plain,(
    ! [A_3,C_71] :
      ( r1_tarski(k1_tarski(A_3),C_71)
      | ~ r2_hidden(A_3,C_71)
      | ~ r2_hidden(A_3,C_71) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_79])).

tff(c_38,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_36,plain,(
    v2_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_40,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_75,plain,(
    ! [A_66,B_67,C_68] :
      ( k9_subset_1(A_66,B_67,C_68) = k3_xboole_0(B_67,C_68)
      | ~ m1_subset_1(C_68,k1_zfmisc_1(A_66)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_78,plain,(
    ! [B_67] : k9_subset_1(u1_struct_0('#skF_3'),B_67,'#skF_4') = k3_xboole_0(B_67,'#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_75])).

tff(c_14,plain,(
    ! [A_9,B_10,C_11] :
      ( m1_subset_1(k9_subset_1(A_9,B_10,C_11),k1_zfmisc_1(A_9))
      | ~ m1_subset_1(C_11,k1_zfmisc_1(A_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_499,plain,(
    ! [A_121,B_122,C_123] :
      ( v4_pre_topc('#skF_1'(A_121,B_122,C_123),A_121)
      | ~ r1_tarski(C_123,B_122)
      | ~ m1_subset_1(C_123,k1_zfmisc_1(u1_struct_0(A_121)))
      | ~ v2_tex_2(B_122,A_121)
      | ~ m1_subset_1(B_122,k1_zfmisc_1(u1_struct_0(A_121)))
      | ~ l1_pre_topc(A_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_2938,plain,(
    ! [A_397,B_398,B_399,C_400] :
      ( v4_pre_topc('#skF_1'(A_397,B_398,k9_subset_1(u1_struct_0(A_397),B_399,C_400)),A_397)
      | ~ r1_tarski(k9_subset_1(u1_struct_0(A_397),B_399,C_400),B_398)
      | ~ v2_tex_2(B_398,A_397)
      | ~ m1_subset_1(B_398,k1_zfmisc_1(u1_struct_0(A_397)))
      | ~ l1_pre_topc(A_397)
      | ~ m1_subset_1(C_400,k1_zfmisc_1(u1_struct_0(A_397))) ) ),
    inference(resolution,[status(thm)],[c_14,c_499])).

tff(c_2968,plain,(
    ! [B_398,B_67] :
      ( v4_pre_topc('#skF_1'('#skF_3',B_398,k3_xboole_0(B_67,'#skF_4')),'#skF_3')
      | ~ r1_tarski(k9_subset_1(u1_struct_0('#skF_3'),B_67,'#skF_4'),B_398)
      | ~ v2_tex_2(B_398,'#skF_3')
      | ~ m1_subset_1(B_398,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_2938])).

tff(c_2988,plain,(
    ! [B_398,B_67] :
      ( v4_pre_topc('#skF_1'('#skF_3',B_398,k3_xboole_0(B_67,'#skF_4')),'#skF_3')
      | ~ r1_tarski(k3_xboole_0(B_67,'#skF_4'),B_398)
      | ~ v2_tex_2(B_398,'#skF_3')
      | ~ m1_subset_1(B_398,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_40,c_78,c_2968])).

tff(c_122,plain,(
    ! [A_77,B_78,C_79] :
      ( m1_subset_1(k9_subset_1(A_77,B_78,C_79),k1_zfmisc_1(A_77))
      | ~ m1_subset_1(C_79,k1_zfmisc_1(A_77)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_131,plain,(
    ! [B_67] :
      ( m1_subset_1(k3_xboole_0(B_67,'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_122])).

tff(c_135,plain,(
    ! [B_67] : m1_subset_1(k3_xboole_0(B_67,'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_131])).

tff(c_942,plain,(
    ! [A_183,B_184,C_185] :
      ( k9_subset_1(u1_struct_0(A_183),B_184,'#skF_1'(A_183,B_184,C_185)) = C_185
      | ~ r1_tarski(C_185,B_184)
      | ~ m1_subset_1(C_185,k1_zfmisc_1(u1_struct_0(A_183)))
      | ~ v2_tex_2(B_184,A_183)
      | ~ m1_subset_1(B_184,k1_zfmisc_1(u1_struct_0(A_183)))
      | ~ l1_pre_topc(A_183) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_3422,plain,(
    ! [A_464,B_465,B_466,C_467] :
      ( k9_subset_1(u1_struct_0(A_464),B_465,'#skF_1'(A_464,B_465,k9_subset_1(u1_struct_0(A_464),B_466,C_467))) = k9_subset_1(u1_struct_0(A_464),B_466,C_467)
      | ~ r1_tarski(k9_subset_1(u1_struct_0(A_464),B_466,C_467),B_465)
      | ~ v2_tex_2(B_465,A_464)
      | ~ m1_subset_1(B_465,k1_zfmisc_1(u1_struct_0(A_464)))
      | ~ l1_pre_topc(A_464)
      | ~ m1_subset_1(C_467,k1_zfmisc_1(u1_struct_0(A_464))) ) ),
    inference(resolution,[status(thm)],[c_14,c_942])).

tff(c_3497,plain,(
    ! [B_465,B_67] :
      ( k9_subset_1(u1_struct_0('#skF_3'),B_465,'#skF_1'('#skF_3',B_465,k3_xboole_0(B_67,'#skF_4'))) = k9_subset_1(u1_struct_0('#skF_3'),B_67,'#skF_4')
      | ~ r1_tarski(k9_subset_1(u1_struct_0('#skF_3'),B_67,'#skF_4'),B_465)
      | ~ v2_tex_2(B_465,'#skF_3')
      | ~ m1_subset_1(B_465,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_3422])).

tff(c_4878,plain,(
    ! [B_625,B_626] :
      ( k9_subset_1(u1_struct_0('#skF_3'),B_625,'#skF_1'('#skF_3',B_625,k3_xboole_0(B_626,'#skF_4'))) = k3_xboole_0(B_626,'#skF_4')
      | ~ r1_tarski(k3_xboole_0(B_626,'#skF_4'),B_625)
      | ~ v2_tex_2(B_625,'#skF_3')
      | ~ m1_subset_1(B_625,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_40,c_78,c_78,c_3497])).

tff(c_658,plain,(
    ! [A_144,B_145,C_146] :
      ( m1_subset_1('#skF_1'(A_144,B_145,C_146),k1_zfmisc_1(u1_struct_0(A_144)))
      | ~ r1_tarski(C_146,B_145)
      | ~ m1_subset_1(C_146,k1_zfmisc_1(u1_struct_0(A_144)))
      | ~ v2_tex_2(B_145,A_144)
      | ~ m1_subset_1(B_145,k1_zfmisc_1(u1_struct_0(A_144)))
      | ~ l1_pre_topc(A_144) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_30,plain,(
    ! [D_51] :
      ( k9_subset_1(u1_struct_0('#skF_3'),'#skF_4',D_51) != k1_tarski('#skF_5')
      | ~ v4_pre_topc(D_51,'#skF_3')
      | ~ m1_subset_1(D_51,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_668,plain,(
    ! [B_145,C_146] :
      ( k9_subset_1(u1_struct_0('#skF_3'),'#skF_4','#skF_1'('#skF_3',B_145,C_146)) != k1_tarski('#skF_5')
      | ~ v4_pre_topc('#skF_1'('#skF_3',B_145,C_146),'#skF_3')
      | ~ r1_tarski(C_146,B_145)
      | ~ m1_subset_1(C_146,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v2_tex_2(B_145,'#skF_3')
      | ~ m1_subset_1(B_145,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_658,c_30])).

tff(c_674,plain,(
    ! [B_145,C_146] :
      ( k9_subset_1(u1_struct_0('#skF_3'),'#skF_4','#skF_1'('#skF_3',B_145,C_146)) != k1_tarski('#skF_5')
      | ~ v4_pre_topc('#skF_1'('#skF_3',B_145,C_146),'#skF_3')
      | ~ r1_tarski(C_146,B_145)
      | ~ m1_subset_1(C_146,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v2_tex_2(B_145,'#skF_3')
      | ~ m1_subset_1(B_145,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_668])).

tff(c_4893,plain,(
    ! [B_626] :
      ( k3_xboole_0(B_626,'#skF_4') != k1_tarski('#skF_5')
      | ~ v4_pre_topc('#skF_1'('#skF_3','#skF_4',k3_xboole_0(B_626,'#skF_4')),'#skF_3')
      | ~ r1_tarski(k3_xboole_0(B_626,'#skF_4'),'#skF_4')
      | ~ m1_subset_1(k3_xboole_0(B_626,'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v2_tex_2('#skF_4','#skF_3')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ r1_tarski(k3_xboole_0(B_626,'#skF_4'),'#skF_4')
      | ~ v2_tex_2('#skF_4','#skF_3')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4878,c_674])).

tff(c_4943,plain,(
    ! [B_631] :
      ( k3_xboole_0(B_631,'#skF_4') != k1_tarski('#skF_5')
      | ~ v4_pre_topc('#skF_1'('#skF_3','#skF_4',k3_xboole_0(B_631,'#skF_4')),'#skF_3')
      | ~ r1_tarski(k3_xboole_0(B_631,'#skF_4'),'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_38,c_36,c_135,c_4893])).

tff(c_4947,plain,(
    ! [B_67] :
      ( k3_xboole_0(B_67,'#skF_4') != k1_tarski('#skF_5')
      | ~ r1_tarski(k3_xboole_0(B_67,'#skF_4'),'#skF_4')
      | ~ v2_tex_2('#skF_4','#skF_3')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(resolution,[status(thm)],[c_2988,c_4943])).

tff(c_4959,plain,(
    ! [B_632] :
      ( k3_xboole_0(B_632,'#skF_4') != k1_tarski('#skF_5')
      | ~ r1_tarski(k3_xboole_0(B_632,'#skF_4'),'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_4947])).

tff(c_4968,plain,(
    ! [A_633] :
      ( k3_xboole_0(k1_tarski(A_633),'#skF_4') != k1_tarski('#skF_5')
      | ~ r1_tarski(k1_tarski(A_633),'#skF_4')
      | ~ r2_hidden(A_633,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_4959])).

tff(c_4974,plain,(
    ! [A_634] :
      ( k3_xboole_0(k1_tarski(A_634),'#skF_4') != k1_tarski('#skF_5')
      | ~ r2_hidden(A_634,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_91,c_4968])).

tff(c_4979,plain,(
    ! [A_635] :
      ( k1_tarski(A_635) != k1_tarski('#skF_5')
      | ~ r2_hidden(A_635,'#skF_4')
      | ~ r2_hidden(A_635,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_4974])).

tff(c_4981,plain,(
    ~ r2_hidden('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_4979])).

tff(c_4985,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_4981])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n025.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 15:54:05 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.90/2.47  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.90/2.47  
% 6.90/2.47  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.90/2.47  %$ v4_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > l1_pre_topc > k2_enumset1 > k9_subset_1 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2
% 6.90/2.47  
% 6.90/2.47  %Foreground sorts:
% 6.90/2.47  
% 6.90/2.47  
% 6.90/2.47  %Background operators:
% 6.90/2.47  
% 6.90/2.47  
% 6.90/2.47  %Foreground operators:
% 6.90/2.47  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 6.90/2.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.90/2.47  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.90/2.47  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.90/2.47  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 6.90/2.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.90/2.47  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.90/2.47  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.90/2.47  tff('#skF_5', type, '#skF_5': $i).
% 6.90/2.47  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 6.90/2.47  tff('#skF_3', type, '#skF_3': $i).
% 6.90/2.47  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.90/2.47  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 6.90/2.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.90/2.47  tff('#skF_4', type, '#skF_4': $i).
% 6.90/2.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.90/2.47  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 6.90/2.47  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.90/2.47  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 6.90/2.47  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 6.90/2.47  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.90/2.47  
% 6.90/2.49  tff(f_90, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ~(r2_hidden(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v4_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = k1_tarski(C))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_tex_2)).
% 6.90/2.49  tff(f_31, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 6.90/2.49  tff(f_39, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 6.90/2.49  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 6.90/2.49  tff(f_47, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 6.90/2.49  tff(f_43, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => m1_subset_1(k9_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 6.90/2.49  tff(f_68, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r1_tarski(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v4_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = C)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_tex_2)).
% 6.90/2.49  tff(c_32, plain, (r2_hidden('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_90])).
% 6.90/2.49  tff(c_4, plain, (![A_3]: (k2_tarski(A_3, A_3)=k1_tarski(A_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.90/2.49  tff(c_79, plain, (![A_69, B_70, C_71]: (r1_tarski(k2_tarski(A_69, B_70), C_71) | ~r2_hidden(B_70, C_71) | ~r2_hidden(A_69, C_71))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.90/2.49  tff(c_104, plain, (![A_73, C_74]: (r1_tarski(k1_tarski(A_73), C_74) | ~r2_hidden(A_73, C_74) | ~r2_hidden(A_73, C_74))), inference(superposition, [status(thm), theory('equality')], [c_4, c_79])).
% 6.90/2.49  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=A_1 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.90/2.49  tff(c_112, plain, (![A_73, C_74]: (k3_xboole_0(k1_tarski(A_73), C_74)=k1_tarski(A_73) | ~r2_hidden(A_73, C_74))), inference(resolution, [status(thm)], [c_104, c_2])).
% 6.90/2.49  tff(c_91, plain, (![A_3, C_71]: (r1_tarski(k1_tarski(A_3), C_71) | ~r2_hidden(A_3, C_71) | ~r2_hidden(A_3, C_71))), inference(superposition, [status(thm), theory('equality')], [c_4, c_79])).
% 6.90/2.49  tff(c_38, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_90])).
% 6.90/2.49  tff(c_36, plain, (v2_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_90])).
% 6.90/2.49  tff(c_40, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_90])).
% 6.90/2.49  tff(c_75, plain, (![A_66, B_67, C_68]: (k9_subset_1(A_66, B_67, C_68)=k3_xboole_0(B_67, C_68) | ~m1_subset_1(C_68, k1_zfmisc_1(A_66)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.90/2.49  tff(c_78, plain, (![B_67]: (k9_subset_1(u1_struct_0('#skF_3'), B_67, '#skF_4')=k3_xboole_0(B_67, '#skF_4'))), inference(resolution, [status(thm)], [c_38, c_75])).
% 6.90/2.49  tff(c_14, plain, (![A_9, B_10, C_11]: (m1_subset_1(k9_subset_1(A_9, B_10, C_11), k1_zfmisc_1(A_9)) | ~m1_subset_1(C_11, k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.90/2.49  tff(c_499, plain, (![A_121, B_122, C_123]: (v4_pre_topc('#skF_1'(A_121, B_122, C_123), A_121) | ~r1_tarski(C_123, B_122) | ~m1_subset_1(C_123, k1_zfmisc_1(u1_struct_0(A_121))) | ~v2_tex_2(B_122, A_121) | ~m1_subset_1(B_122, k1_zfmisc_1(u1_struct_0(A_121))) | ~l1_pre_topc(A_121))), inference(cnfTransformation, [status(thm)], [f_68])).
% 6.90/2.49  tff(c_2938, plain, (![A_397, B_398, B_399, C_400]: (v4_pre_topc('#skF_1'(A_397, B_398, k9_subset_1(u1_struct_0(A_397), B_399, C_400)), A_397) | ~r1_tarski(k9_subset_1(u1_struct_0(A_397), B_399, C_400), B_398) | ~v2_tex_2(B_398, A_397) | ~m1_subset_1(B_398, k1_zfmisc_1(u1_struct_0(A_397))) | ~l1_pre_topc(A_397) | ~m1_subset_1(C_400, k1_zfmisc_1(u1_struct_0(A_397))))), inference(resolution, [status(thm)], [c_14, c_499])).
% 6.90/2.49  tff(c_2968, plain, (![B_398, B_67]: (v4_pre_topc('#skF_1'('#skF_3', B_398, k3_xboole_0(B_67, '#skF_4')), '#skF_3') | ~r1_tarski(k9_subset_1(u1_struct_0('#skF_3'), B_67, '#skF_4'), B_398) | ~v2_tex_2(B_398, '#skF_3') | ~m1_subset_1(B_398, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(superposition, [status(thm), theory('equality')], [c_78, c_2938])).
% 6.90/2.49  tff(c_2988, plain, (![B_398, B_67]: (v4_pre_topc('#skF_1'('#skF_3', B_398, k3_xboole_0(B_67, '#skF_4')), '#skF_3') | ~r1_tarski(k3_xboole_0(B_67, '#skF_4'), B_398) | ~v2_tex_2(B_398, '#skF_3') | ~m1_subset_1(B_398, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_40, c_78, c_2968])).
% 6.90/2.49  tff(c_122, plain, (![A_77, B_78, C_79]: (m1_subset_1(k9_subset_1(A_77, B_78, C_79), k1_zfmisc_1(A_77)) | ~m1_subset_1(C_79, k1_zfmisc_1(A_77)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.90/2.49  tff(c_131, plain, (![B_67]: (m1_subset_1(k3_xboole_0(B_67, '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(superposition, [status(thm), theory('equality')], [c_78, c_122])).
% 6.90/2.49  tff(c_135, plain, (![B_67]: (m1_subset_1(k3_xboole_0(B_67, '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_131])).
% 6.90/2.49  tff(c_942, plain, (![A_183, B_184, C_185]: (k9_subset_1(u1_struct_0(A_183), B_184, '#skF_1'(A_183, B_184, C_185))=C_185 | ~r1_tarski(C_185, B_184) | ~m1_subset_1(C_185, k1_zfmisc_1(u1_struct_0(A_183))) | ~v2_tex_2(B_184, A_183) | ~m1_subset_1(B_184, k1_zfmisc_1(u1_struct_0(A_183))) | ~l1_pre_topc(A_183))), inference(cnfTransformation, [status(thm)], [f_68])).
% 6.90/2.49  tff(c_3422, plain, (![A_464, B_465, B_466, C_467]: (k9_subset_1(u1_struct_0(A_464), B_465, '#skF_1'(A_464, B_465, k9_subset_1(u1_struct_0(A_464), B_466, C_467)))=k9_subset_1(u1_struct_0(A_464), B_466, C_467) | ~r1_tarski(k9_subset_1(u1_struct_0(A_464), B_466, C_467), B_465) | ~v2_tex_2(B_465, A_464) | ~m1_subset_1(B_465, k1_zfmisc_1(u1_struct_0(A_464))) | ~l1_pre_topc(A_464) | ~m1_subset_1(C_467, k1_zfmisc_1(u1_struct_0(A_464))))), inference(resolution, [status(thm)], [c_14, c_942])).
% 6.90/2.49  tff(c_3497, plain, (![B_465, B_67]: (k9_subset_1(u1_struct_0('#skF_3'), B_465, '#skF_1'('#skF_3', B_465, k3_xboole_0(B_67, '#skF_4')))=k9_subset_1(u1_struct_0('#skF_3'), B_67, '#skF_4') | ~r1_tarski(k9_subset_1(u1_struct_0('#skF_3'), B_67, '#skF_4'), B_465) | ~v2_tex_2(B_465, '#skF_3') | ~m1_subset_1(B_465, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(superposition, [status(thm), theory('equality')], [c_78, c_3422])).
% 6.90/2.49  tff(c_4878, plain, (![B_625, B_626]: (k9_subset_1(u1_struct_0('#skF_3'), B_625, '#skF_1'('#skF_3', B_625, k3_xboole_0(B_626, '#skF_4')))=k3_xboole_0(B_626, '#skF_4') | ~r1_tarski(k3_xboole_0(B_626, '#skF_4'), B_625) | ~v2_tex_2(B_625, '#skF_3') | ~m1_subset_1(B_625, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_40, c_78, c_78, c_3497])).
% 6.90/2.49  tff(c_658, plain, (![A_144, B_145, C_146]: (m1_subset_1('#skF_1'(A_144, B_145, C_146), k1_zfmisc_1(u1_struct_0(A_144))) | ~r1_tarski(C_146, B_145) | ~m1_subset_1(C_146, k1_zfmisc_1(u1_struct_0(A_144))) | ~v2_tex_2(B_145, A_144) | ~m1_subset_1(B_145, k1_zfmisc_1(u1_struct_0(A_144))) | ~l1_pre_topc(A_144))), inference(cnfTransformation, [status(thm)], [f_68])).
% 6.90/2.49  tff(c_30, plain, (![D_51]: (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', D_51)!=k1_tarski('#skF_5') | ~v4_pre_topc(D_51, '#skF_3') | ~m1_subset_1(D_51, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 6.90/2.49  tff(c_668, plain, (![B_145, C_146]: (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', '#skF_1'('#skF_3', B_145, C_146))!=k1_tarski('#skF_5') | ~v4_pre_topc('#skF_1'('#skF_3', B_145, C_146), '#skF_3') | ~r1_tarski(C_146, B_145) | ~m1_subset_1(C_146, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v2_tex_2(B_145, '#skF_3') | ~m1_subset_1(B_145, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_658, c_30])).
% 6.90/2.49  tff(c_674, plain, (![B_145, C_146]: (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', '#skF_1'('#skF_3', B_145, C_146))!=k1_tarski('#skF_5') | ~v4_pre_topc('#skF_1'('#skF_3', B_145, C_146), '#skF_3') | ~r1_tarski(C_146, B_145) | ~m1_subset_1(C_146, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v2_tex_2(B_145, '#skF_3') | ~m1_subset_1(B_145, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_668])).
% 6.90/2.49  tff(c_4893, plain, (![B_626]: (k3_xboole_0(B_626, '#skF_4')!=k1_tarski('#skF_5') | ~v4_pre_topc('#skF_1'('#skF_3', '#skF_4', k3_xboole_0(B_626, '#skF_4')), '#skF_3') | ~r1_tarski(k3_xboole_0(B_626, '#skF_4'), '#skF_4') | ~m1_subset_1(k3_xboole_0(B_626, '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v2_tex_2('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~r1_tarski(k3_xboole_0(B_626, '#skF_4'), '#skF_4') | ~v2_tex_2('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(superposition, [status(thm), theory('equality')], [c_4878, c_674])).
% 6.90/2.49  tff(c_4943, plain, (![B_631]: (k3_xboole_0(B_631, '#skF_4')!=k1_tarski('#skF_5') | ~v4_pre_topc('#skF_1'('#skF_3', '#skF_4', k3_xboole_0(B_631, '#skF_4')), '#skF_3') | ~r1_tarski(k3_xboole_0(B_631, '#skF_4'), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_38, c_36, c_135, c_4893])).
% 6.90/2.49  tff(c_4947, plain, (![B_67]: (k3_xboole_0(B_67, '#skF_4')!=k1_tarski('#skF_5') | ~r1_tarski(k3_xboole_0(B_67, '#skF_4'), '#skF_4') | ~v2_tex_2('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(resolution, [status(thm)], [c_2988, c_4943])).
% 6.90/2.49  tff(c_4959, plain, (![B_632]: (k3_xboole_0(B_632, '#skF_4')!=k1_tarski('#skF_5') | ~r1_tarski(k3_xboole_0(B_632, '#skF_4'), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_4947])).
% 6.90/2.49  tff(c_4968, plain, (![A_633]: (k3_xboole_0(k1_tarski(A_633), '#skF_4')!=k1_tarski('#skF_5') | ~r1_tarski(k1_tarski(A_633), '#skF_4') | ~r2_hidden(A_633, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_112, c_4959])).
% 6.90/2.49  tff(c_4974, plain, (![A_634]: (k3_xboole_0(k1_tarski(A_634), '#skF_4')!=k1_tarski('#skF_5') | ~r2_hidden(A_634, '#skF_4'))), inference(resolution, [status(thm)], [c_91, c_4968])).
% 6.90/2.49  tff(c_4979, plain, (![A_635]: (k1_tarski(A_635)!=k1_tarski('#skF_5') | ~r2_hidden(A_635, '#skF_4') | ~r2_hidden(A_635, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_112, c_4974])).
% 6.90/2.49  tff(c_4981, plain, (~r2_hidden('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_32, c_4979])).
% 6.90/2.49  tff(c_4985, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_4981])).
% 6.90/2.49  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.90/2.49  
% 6.90/2.49  Inference rules
% 6.90/2.49  ----------------------
% 6.90/2.49  #Ref     : 0
% 6.90/2.49  #Sup     : 1235
% 6.90/2.49  #Fact    : 0
% 6.90/2.49  #Define  : 0
% 6.90/2.49  #Split   : 2
% 6.90/2.49  #Chain   : 0
% 6.90/2.49  #Close   : 0
% 6.90/2.49  
% 6.90/2.49  Ordering : KBO
% 6.90/2.49  
% 6.90/2.49  Simplification rules
% 6.90/2.49  ----------------------
% 6.90/2.49  #Subsume      : 130
% 6.90/2.49  #Demod        : 390
% 6.90/2.49  #Tautology    : 116
% 6.90/2.49  #SimpNegUnit  : 0
% 6.90/2.49  #BackRed      : 2
% 6.90/2.49  
% 6.90/2.49  #Partial instantiations: 0
% 6.90/2.49  #Strategies tried      : 1
% 6.90/2.49  
% 6.90/2.49  Timing (in seconds)
% 6.90/2.49  ----------------------
% 6.90/2.49  Preprocessing        : 0.29
% 6.90/2.49  Parsing              : 0.15
% 6.90/2.49  CNF conversion       : 0.02
% 6.90/2.49  Main loop            : 1.44
% 6.90/2.49  Inferencing          : 0.53
% 6.90/2.49  Reduction            : 0.42
% 6.90/2.49  Demodulation         : 0.30
% 6.90/2.49  BG Simplification    : 0.07
% 6.90/2.49  Subsumption          : 0.33
% 6.90/2.49  Abstraction          : 0.08
% 6.90/2.49  MUC search           : 0.00
% 6.90/2.49  Cooper               : 0.00
% 6.90/2.49  Total                : 1.76
% 6.90/2.49  Index Insertion      : 0.00
% 6.90/2.49  Index Deletion       : 0.00
% 6.90/2.49  Index Matching       : 0.00
% 6.90/2.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
