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
% DateTime   : Thu Dec  3 10:29:20 EST 2020

% Result     : Theorem 3.75s
% Output     : CNFRefutation 3.75s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 103 expanded)
%              Number of leaves         :   26 (  52 expanded)
%              Depth                    :   15
%              Number of atoms          :  159 ( 388 expanded)
%              Number of equality atoms :   21 (  48 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

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

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_99,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_tex_2)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_77,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tex_2(B,A)
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ~ ( r2_hidden(C,B)
                    & ! [D] :
                        ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                       => ~ ( v3_pre_topc(D,A)
                            & k9_subset_1(u1_struct_0(A),B,D) = k1_tarski(C) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_tex_2)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => m1_subset_1(k9_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).

tff(f_56,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_tex_2)).

tff(c_30,plain,(
    r2_hidden('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_32,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_6,plain,(
    ! [A_2,B_3] :
      ( r1_tarski(k1_tarski(A_2),B_3)
      | ~ r2_hidden(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_38,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_34,plain,(
    v2_tex_2('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_36,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_218,plain,(
    ! [A_94,B_95,C_96] :
      ( k9_subset_1(u1_struct_0(A_94),B_95,'#skF_3'(A_94,B_95,C_96)) = k1_tarski(C_96)
      | ~ r2_hidden(C_96,B_95)
      | ~ m1_subset_1(C_96,u1_struct_0(A_94))
      | ~ v2_tex_2(B_95,A_94)
      | ~ m1_subset_1(B_95,k1_zfmisc_1(u1_struct_0(A_94)))
      | ~ l1_pre_topc(A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_229,plain,(
    ! [C_96] :
      ( k9_subset_1(u1_struct_0('#skF_4'),'#skF_5','#skF_3'('#skF_4','#skF_5',C_96)) = k1_tarski(C_96)
      | ~ r2_hidden(C_96,'#skF_5')
      | ~ m1_subset_1(C_96,u1_struct_0('#skF_4'))
      | ~ v2_tex_2('#skF_5','#skF_4')
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_36,c_218])).

tff(c_236,plain,(
    ! [C_96] :
      ( k9_subset_1(u1_struct_0('#skF_4'),'#skF_5','#skF_3'('#skF_4','#skF_5',C_96)) = k1_tarski(C_96)
      | ~ r2_hidden(C_96,'#skF_5')
      | ~ m1_subset_1(C_96,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_34,c_229])).

tff(c_26,plain,(
    ! [A_32,B_40,C_44] :
      ( m1_subset_1('#skF_3'(A_32,B_40,C_44),k1_zfmisc_1(u1_struct_0(A_32)))
      | ~ r2_hidden(C_44,B_40)
      | ~ m1_subset_1(C_44,u1_struct_0(A_32))
      | ~ v2_tex_2(B_40,A_32)
      | ~ m1_subset_1(B_40,k1_zfmisc_1(u1_struct_0(A_32)))
      | ~ l1_pre_topc(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_8,plain,(
    ! [A_4,B_5,C_6] :
      ( m1_subset_1(k9_subset_1(A_4,B_5,C_6),k1_zfmisc_1(A_4))
      | ~ m1_subset_1(C_6,k1_zfmisc_1(A_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_120,plain,(
    ! [A_78,B_79,C_80] :
      ( v4_pre_topc('#skF_1'(A_78,B_79,C_80),A_78)
      | ~ r1_tarski(C_80,B_79)
      | ~ m1_subset_1(C_80,k1_zfmisc_1(u1_struct_0(A_78)))
      | ~ v2_tex_2(B_79,A_78)
      | ~ m1_subset_1(B_79,k1_zfmisc_1(u1_struct_0(A_78)))
      | ~ l1_pre_topc(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_129,plain,(
    ! [A_78,B_79,B_5,C_6] :
      ( v4_pre_topc('#skF_1'(A_78,B_79,k9_subset_1(u1_struct_0(A_78),B_5,C_6)),A_78)
      | ~ r1_tarski(k9_subset_1(u1_struct_0(A_78),B_5,C_6),B_79)
      | ~ v2_tex_2(B_79,A_78)
      | ~ m1_subset_1(B_79,k1_zfmisc_1(u1_struct_0(A_78)))
      | ~ l1_pre_topc(A_78)
      | ~ m1_subset_1(C_6,k1_zfmisc_1(u1_struct_0(A_78))) ) ),
    inference(resolution,[status(thm)],[c_8,c_120])).

tff(c_296,plain,(
    ! [A_103,B_104,C_105] :
      ( k9_subset_1(u1_struct_0(A_103),B_104,'#skF_1'(A_103,B_104,C_105)) = C_105
      | ~ r1_tarski(C_105,B_104)
      | ~ m1_subset_1(C_105,k1_zfmisc_1(u1_struct_0(A_103)))
      | ~ v2_tex_2(B_104,A_103)
      | ~ m1_subset_1(B_104,k1_zfmisc_1(u1_struct_0(A_103)))
      | ~ l1_pre_topc(A_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_815,plain,(
    ! [A_177,B_178,B_179,C_180] :
      ( k9_subset_1(u1_struct_0(A_177),B_178,'#skF_1'(A_177,B_178,k9_subset_1(u1_struct_0(A_177),B_179,C_180))) = k9_subset_1(u1_struct_0(A_177),B_179,C_180)
      | ~ r1_tarski(k9_subset_1(u1_struct_0(A_177),B_179,C_180),B_178)
      | ~ v2_tex_2(B_178,A_177)
      | ~ m1_subset_1(B_178,k1_zfmisc_1(u1_struct_0(A_177)))
      | ~ l1_pre_topc(A_177)
      | ~ m1_subset_1(C_180,k1_zfmisc_1(u1_struct_0(A_177))) ) ),
    inference(resolution,[status(thm)],[c_8,c_296])).

tff(c_185,plain,(
    ! [A_87,B_88,C_89] :
      ( m1_subset_1('#skF_1'(A_87,B_88,C_89),k1_zfmisc_1(u1_struct_0(A_87)))
      | ~ r1_tarski(C_89,B_88)
      | ~ m1_subset_1(C_89,k1_zfmisc_1(u1_struct_0(A_87)))
      | ~ v2_tex_2(B_88,A_87)
      | ~ m1_subset_1(B_88,k1_zfmisc_1(u1_struct_0(A_87)))
      | ~ l1_pre_topc(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_28,plain,(
    ! [D_57] :
      ( k9_subset_1(u1_struct_0('#skF_4'),'#skF_5',D_57) != k1_tarski('#skF_6')
      | ~ v4_pre_topc(D_57,'#skF_4')
      | ~ m1_subset_1(D_57,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_203,plain,(
    ! [B_88,C_89] :
      ( k9_subset_1(u1_struct_0('#skF_4'),'#skF_5','#skF_1'('#skF_4',B_88,C_89)) != k1_tarski('#skF_6')
      | ~ v4_pre_topc('#skF_1'('#skF_4',B_88,C_89),'#skF_4')
      | ~ r1_tarski(C_89,B_88)
      | ~ m1_subset_1(C_89,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v2_tex_2(B_88,'#skF_4')
      | ~ m1_subset_1(B_88,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_185,c_28])).

tff(c_215,plain,(
    ! [B_88,C_89] :
      ( k9_subset_1(u1_struct_0('#skF_4'),'#skF_5','#skF_1'('#skF_4',B_88,C_89)) != k1_tarski('#skF_6')
      | ~ v4_pre_topc('#skF_1'('#skF_4',B_88,C_89),'#skF_4')
      | ~ r1_tarski(C_89,B_88)
      | ~ m1_subset_1(C_89,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v2_tex_2(B_88,'#skF_4')
      | ~ m1_subset_1(B_88,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_203])).

tff(c_846,plain,(
    ! [B_179,C_180] :
      ( k9_subset_1(u1_struct_0('#skF_4'),B_179,C_180) != k1_tarski('#skF_6')
      | ~ v4_pre_topc('#skF_1'('#skF_4','#skF_5',k9_subset_1(u1_struct_0('#skF_4'),B_179,C_180)),'#skF_4')
      | ~ r1_tarski(k9_subset_1(u1_struct_0('#skF_4'),B_179,C_180),'#skF_5')
      | ~ m1_subset_1(k9_subset_1(u1_struct_0('#skF_4'),B_179,C_180),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v2_tex_2('#skF_5','#skF_4')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_tarski(k9_subset_1(u1_struct_0('#skF_4'),B_179,C_180),'#skF_5')
      | ~ v2_tex_2('#skF_5','#skF_4')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4')
      | ~ m1_subset_1(C_180,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_815,c_215])).

tff(c_918,plain,(
    ! [B_182,C_183] :
      ( k9_subset_1(u1_struct_0('#skF_4'),B_182,C_183) != k1_tarski('#skF_6')
      | ~ v4_pre_topc('#skF_1'('#skF_4','#skF_5',k9_subset_1(u1_struct_0('#skF_4'),B_182,C_183)),'#skF_4')
      | ~ m1_subset_1(k9_subset_1(u1_struct_0('#skF_4'),B_182,C_183),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_tarski(k9_subset_1(u1_struct_0('#skF_4'),B_182,C_183),'#skF_5')
      | ~ m1_subset_1(C_183,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_36,c_34,c_846])).

tff(c_960,plain,(
    ! [B_184,C_185] :
      ( k9_subset_1(u1_struct_0('#skF_4'),B_184,C_185) != k1_tarski('#skF_6')
      | ~ v4_pre_topc('#skF_1'('#skF_4','#skF_5',k9_subset_1(u1_struct_0('#skF_4'),B_184,C_185)),'#skF_4')
      | ~ r1_tarski(k9_subset_1(u1_struct_0('#skF_4'),B_184,C_185),'#skF_5')
      | ~ m1_subset_1(C_185,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_8,c_918])).

tff(c_982,plain,(
    ! [B_5,C_6] :
      ( k9_subset_1(u1_struct_0('#skF_4'),B_5,C_6) != k1_tarski('#skF_6')
      | ~ r1_tarski(k9_subset_1(u1_struct_0('#skF_4'),B_5,C_6),'#skF_5')
      | ~ v2_tex_2('#skF_5','#skF_4')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4')
      | ~ m1_subset_1(C_6,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_129,c_960])).

tff(c_1002,plain,(
    ! [B_187,C_188] :
      ( k9_subset_1(u1_struct_0('#skF_4'),B_187,C_188) != k1_tarski('#skF_6')
      | ~ r1_tarski(k9_subset_1(u1_struct_0('#skF_4'),B_187,C_188),'#skF_5')
      | ~ m1_subset_1(C_188,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_982])).

tff(c_1033,plain,(
    ! [C_189] :
      ( k9_subset_1(u1_struct_0('#skF_4'),'#skF_5','#skF_3'('#skF_4','#skF_5',C_189)) != k1_tarski('#skF_6')
      | ~ r1_tarski(k1_tarski(C_189),'#skF_5')
      | ~ m1_subset_1('#skF_3'('#skF_4','#skF_5',C_189),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r2_hidden(C_189,'#skF_5')
      | ~ m1_subset_1(C_189,u1_struct_0('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_236,c_1002])).

tff(c_1037,plain,(
    ! [C_44] :
      ( k9_subset_1(u1_struct_0('#skF_4'),'#skF_5','#skF_3'('#skF_4','#skF_5',C_44)) != k1_tarski('#skF_6')
      | ~ r1_tarski(k1_tarski(C_44),'#skF_5')
      | ~ r2_hidden(C_44,'#skF_5')
      | ~ m1_subset_1(C_44,u1_struct_0('#skF_4'))
      | ~ v2_tex_2('#skF_5','#skF_4')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_26,c_1033])).

tff(c_1041,plain,(
    ! [C_190] :
      ( k9_subset_1(u1_struct_0('#skF_4'),'#skF_5','#skF_3'('#skF_4','#skF_5',C_190)) != k1_tarski('#skF_6')
      | ~ r1_tarski(k1_tarski(C_190),'#skF_5')
      | ~ r2_hidden(C_190,'#skF_5')
      | ~ m1_subset_1(C_190,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_1037])).

tff(c_1045,plain,(
    ! [C_191] :
      ( k1_tarski(C_191) != k1_tarski('#skF_6')
      | ~ r1_tarski(k1_tarski(C_191),'#skF_5')
      | ~ r2_hidden(C_191,'#skF_5')
      | ~ m1_subset_1(C_191,u1_struct_0('#skF_4'))
      | ~ r2_hidden(C_191,'#skF_5')
      | ~ m1_subset_1(C_191,u1_struct_0('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_236,c_1041])).

tff(c_1051,plain,(
    ! [A_192] :
      ( k1_tarski(A_192) != k1_tarski('#skF_6')
      | ~ m1_subset_1(A_192,u1_struct_0('#skF_4'))
      | ~ r2_hidden(A_192,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_6,c_1045])).

tff(c_1054,plain,(
    ~ r2_hidden('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_32,c_1051])).

tff(c_1058,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_1054])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n007.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:18:21 EST 2020
% 0.12/0.35  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.75/1.64  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.75/1.65  
% 3.75/1.65  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.75/1.65  %$ v4_pre_topc > v3_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_2
% 3.75/1.65  
% 3.75/1.65  %Foreground sorts:
% 3.75/1.65  
% 3.75/1.65  
% 3.75/1.65  %Background operators:
% 3.75/1.65  
% 3.75/1.65  
% 3.75/1.65  %Foreground operators:
% 3.75/1.65  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.75/1.65  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.75/1.65  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.75/1.65  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.75/1.65  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.75/1.65  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.75/1.65  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.75/1.65  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.75/1.65  tff('#skF_5', type, '#skF_5': $i).
% 3.75/1.65  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 3.75/1.65  tff('#skF_6', type, '#skF_6': $i).
% 3.75/1.65  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.75/1.65  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 3.75/1.65  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.75/1.65  tff('#skF_4', type, '#skF_4': $i).
% 3.75/1.65  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.75/1.65  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.75/1.65  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.75/1.65  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.75/1.65  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 3.75/1.65  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.75/1.65  
% 3.75/1.66  tff(f_99, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ~(r2_hidden(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v4_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = k1_tarski(C))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_tex_2)).
% 3.75/1.66  tff(f_31, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 3.75/1.66  tff(f_77, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ~(r2_hidden(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v3_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = k1_tarski(C))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_tex_2)).
% 3.75/1.66  tff(f_35, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => m1_subset_1(k9_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 3.75/1.66  tff(f_56, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r1_tarski(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v4_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = C)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_tex_2)).
% 3.75/1.66  tff(c_30, plain, (r2_hidden('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.75/1.66  tff(c_32, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.75/1.66  tff(c_6, plain, (![A_2, B_3]: (r1_tarski(k1_tarski(A_2), B_3) | ~r2_hidden(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.75/1.66  tff(c_38, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.75/1.66  tff(c_34, plain, (v2_tex_2('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.75/1.66  tff(c_36, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.75/1.66  tff(c_218, plain, (![A_94, B_95, C_96]: (k9_subset_1(u1_struct_0(A_94), B_95, '#skF_3'(A_94, B_95, C_96))=k1_tarski(C_96) | ~r2_hidden(C_96, B_95) | ~m1_subset_1(C_96, u1_struct_0(A_94)) | ~v2_tex_2(B_95, A_94) | ~m1_subset_1(B_95, k1_zfmisc_1(u1_struct_0(A_94))) | ~l1_pre_topc(A_94))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.75/1.66  tff(c_229, plain, (![C_96]: (k9_subset_1(u1_struct_0('#skF_4'), '#skF_5', '#skF_3'('#skF_4', '#skF_5', C_96))=k1_tarski(C_96) | ~r2_hidden(C_96, '#skF_5') | ~m1_subset_1(C_96, u1_struct_0('#skF_4')) | ~v2_tex_2('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_36, c_218])).
% 3.75/1.66  tff(c_236, plain, (![C_96]: (k9_subset_1(u1_struct_0('#skF_4'), '#skF_5', '#skF_3'('#skF_4', '#skF_5', C_96))=k1_tarski(C_96) | ~r2_hidden(C_96, '#skF_5') | ~m1_subset_1(C_96, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_34, c_229])).
% 3.75/1.66  tff(c_26, plain, (![A_32, B_40, C_44]: (m1_subset_1('#skF_3'(A_32, B_40, C_44), k1_zfmisc_1(u1_struct_0(A_32))) | ~r2_hidden(C_44, B_40) | ~m1_subset_1(C_44, u1_struct_0(A_32)) | ~v2_tex_2(B_40, A_32) | ~m1_subset_1(B_40, k1_zfmisc_1(u1_struct_0(A_32))) | ~l1_pre_topc(A_32))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.75/1.66  tff(c_8, plain, (![A_4, B_5, C_6]: (m1_subset_1(k9_subset_1(A_4, B_5, C_6), k1_zfmisc_1(A_4)) | ~m1_subset_1(C_6, k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.75/1.66  tff(c_120, plain, (![A_78, B_79, C_80]: (v4_pre_topc('#skF_1'(A_78, B_79, C_80), A_78) | ~r1_tarski(C_80, B_79) | ~m1_subset_1(C_80, k1_zfmisc_1(u1_struct_0(A_78))) | ~v2_tex_2(B_79, A_78) | ~m1_subset_1(B_79, k1_zfmisc_1(u1_struct_0(A_78))) | ~l1_pre_topc(A_78))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.75/1.66  tff(c_129, plain, (![A_78, B_79, B_5, C_6]: (v4_pre_topc('#skF_1'(A_78, B_79, k9_subset_1(u1_struct_0(A_78), B_5, C_6)), A_78) | ~r1_tarski(k9_subset_1(u1_struct_0(A_78), B_5, C_6), B_79) | ~v2_tex_2(B_79, A_78) | ~m1_subset_1(B_79, k1_zfmisc_1(u1_struct_0(A_78))) | ~l1_pre_topc(A_78) | ~m1_subset_1(C_6, k1_zfmisc_1(u1_struct_0(A_78))))), inference(resolution, [status(thm)], [c_8, c_120])).
% 3.75/1.66  tff(c_296, plain, (![A_103, B_104, C_105]: (k9_subset_1(u1_struct_0(A_103), B_104, '#skF_1'(A_103, B_104, C_105))=C_105 | ~r1_tarski(C_105, B_104) | ~m1_subset_1(C_105, k1_zfmisc_1(u1_struct_0(A_103))) | ~v2_tex_2(B_104, A_103) | ~m1_subset_1(B_104, k1_zfmisc_1(u1_struct_0(A_103))) | ~l1_pre_topc(A_103))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.75/1.66  tff(c_815, plain, (![A_177, B_178, B_179, C_180]: (k9_subset_1(u1_struct_0(A_177), B_178, '#skF_1'(A_177, B_178, k9_subset_1(u1_struct_0(A_177), B_179, C_180)))=k9_subset_1(u1_struct_0(A_177), B_179, C_180) | ~r1_tarski(k9_subset_1(u1_struct_0(A_177), B_179, C_180), B_178) | ~v2_tex_2(B_178, A_177) | ~m1_subset_1(B_178, k1_zfmisc_1(u1_struct_0(A_177))) | ~l1_pre_topc(A_177) | ~m1_subset_1(C_180, k1_zfmisc_1(u1_struct_0(A_177))))), inference(resolution, [status(thm)], [c_8, c_296])).
% 3.75/1.66  tff(c_185, plain, (![A_87, B_88, C_89]: (m1_subset_1('#skF_1'(A_87, B_88, C_89), k1_zfmisc_1(u1_struct_0(A_87))) | ~r1_tarski(C_89, B_88) | ~m1_subset_1(C_89, k1_zfmisc_1(u1_struct_0(A_87))) | ~v2_tex_2(B_88, A_87) | ~m1_subset_1(B_88, k1_zfmisc_1(u1_struct_0(A_87))) | ~l1_pre_topc(A_87))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.75/1.66  tff(c_28, plain, (![D_57]: (k9_subset_1(u1_struct_0('#skF_4'), '#skF_5', D_57)!=k1_tarski('#skF_6') | ~v4_pre_topc(D_57, '#skF_4') | ~m1_subset_1(D_57, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.75/1.66  tff(c_203, plain, (![B_88, C_89]: (k9_subset_1(u1_struct_0('#skF_4'), '#skF_5', '#skF_1'('#skF_4', B_88, C_89))!=k1_tarski('#skF_6') | ~v4_pre_topc('#skF_1'('#skF_4', B_88, C_89), '#skF_4') | ~r1_tarski(C_89, B_88) | ~m1_subset_1(C_89, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v2_tex_2(B_88, '#skF_4') | ~m1_subset_1(B_88, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_185, c_28])).
% 3.75/1.66  tff(c_215, plain, (![B_88, C_89]: (k9_subset_1(u1_struct_0('#skF_4'), '#skF_5', '#skF_1'('#skF_4', B_88, C_89))!=k1_tarski('#skF_6') | ~v4_pre_topc('#skF_1'('#skF_4', B_88, C_89), '#skF_4') | ~r1_tarski(C_89, B_88) | ~m1_subset_1(C_89, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v2_tex_2(B_88, '#skF_4') | ~m1_subset_1(B_88, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_203])).
% 3.75/1.66  tff(c_846, plain, (![B_179, C_180]: (k9_subset_1(u1_struct_0('#skF_4'), B_179, C_180)!=k1_tarski('#skF_6') | ~v4_pre_topc('#skF_1'('#skF_4', '#skF_5', k9_subset_1(u1_struct_0('#skF_4'), B_179, C_180)), '#skF_4') | ~r1_tarski(k9_subset_1(u1_struct_0('#skF_4'), B_179, C_180), '#skF_5') | ~m1_subset_1(k9_subset_1(u1_struct_0('#skF_4'), B_179, C_180), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v2_tex_2('#skF_5', '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r1_tarski(k9_subset_1(u1_struct_0('#skF_4'), B_179, C_180), '#skF_5') | ~v2_tex_2('#skF_5', '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4') | ~m1_subset_1(C_180, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(superposition, [status(thm), theory('equality')], [c_815, c_215])).
% 3.75/1.66  tff(c_918, plain, (![B_182, C_183]: (k9_subset_1(u1_struct_0('#skF_4'), B_182, C_183)!=k1_tarski('#skF_6') | ~v4_pre_topc('#skF_1'('#skF_4', '#skF_5', k9_subset_1(u1_struct_0('#skF_4'), B_182, C_183)), '#skF_4') | ~m1_subset_1(k9_subset_1(u1_struct_0('#skF_4'), B_182, C_183), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r1_tarski(k9_subset_1(u1_struct_0('#skF_4'), B_182, C_183), '#skF_5') | ~m1_subset_1(C_183, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_36, c_34, c_846])).
% 3.75/1.66  tff(c_960, plain, (![B_184, C_185]: (k9_subset_1(u1_struct_0('#skF_4'), B_184, C_185)!=k1_tarski('#skF_6') | ~v4_pre_topc('#skF_1'('#skF_4', '#skF_5', k9_subset_1(u1_struct_0('#skF_4'), B_184, C_185)), '#skF_4') | ~r1_tarski(k9_subset_1(u1_struct_0('#skF_4'), B_184, C_185), '#skF_5') | ~m1_subset_1(C_185, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_8, c_918])).
% 3.75/1.66  tff(c_982, plain, (![B_5, C_6]: (k9_subset_1(u1_struct_0('#skF_4'), B_5, C_6)!=k1_tarski('#skF_6') | ~r1_tarski(k9_subset_1(u1_struct_0('#skF_4'), B_5, C_6), '#skF_5') | ~v2_tex_2('#skF_5', '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4') | ~m1_subset_1(C_6, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_129, c_960])).
% 3.75/1.66  tff(c_1002, plain, (![B_187, C_188]: (k9_subset_1(u1_struct_0('#skF_4'), B_187, C_188)!=k1_tarski('#skF_6') | ~r1_tarski(k9_subset_1(u1_struct_0('#skF_4'), B_187, C_188), '#skF_5') | ~m1_subset_1(C_188, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_982])).
% 3.75/1.66  tff(c_1033, plain, (![C_189]: (k9_subset_1(u1_struct_0('#skF_4'), '#skF_5', '#skF_3'('#skF_4', '#skF_5', C_189))!=k1_tarski('#skF_6') | ~r1_tarski(k1_tarski(C_189), '#skF_5') | ~m1_subset_1('#skF_3'('#skF_4', '#skF_5', C_189), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r2_hidden(C_189, '#skF_5') | ~m1_subset_1(C_189, u1_struct_0('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_236, c_1002])).
% 3.75/1.66  tff(c_1037, plain, (![C_44]: (k9_subset_1(u1_struct_0('#skF_4'), '#skF_5', '#skF_3'('#skF_4', '#skF_5', C_44))!=k1_tarski('#skF_6') | ~r1_tarski(k1_tarski(C_44), '#skF_5') | ~r2_hidden(C_44, '#skF_5') | ~m1_subset_1(C_44, u1_struct_0('#skF_4')) | ~v2_tex_2('#skF_5', '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_26, c_1033])).
% 3.75/1.66  tff(c_1041, plain, (![C_190]: (k9_subset_1(u1_struct_0('#skF_4'), '#skF_5', '#skF_3'('#skF_4', '#skF_5', C_190))!=k1_tarski('#skF_6') | ~r1_tarski(k1_tarski(C_190), '#skF_5') | ~r2_hidden(C_190, '#skF_5') | ~m1_subset_1(C_190, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_1037])).
% 3.75/1.66  tff(c_1045, plain, (![C_191]: (k1_tarski(C_191)!=k1_tarski('#skF_6') | ~r1_tarski(k1_tarski(C_191), '#skF_5') | ~r2_hidden(C_191, '#skF_5') | ~m1_subset_1(C_191, u1_struct_0('#skF_4')) | ~r2_hidden(C_191, '#skF_5') | ~m1_subset_1(C_191, u1_struct_0('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_236, c_1041])).
% 3.75/1.66  tff(c_1051, plain, (![A_192]: (k1_tarski(A_192)!=k1_tarski('#skF_6') | ~m1_subset_1(A_192, u1_struct_0('#skF_4')) | ~r2_hidden(A_192, '#skF_5'))), inference(resolution, [status(thm)], [c_6, c_1045])).
% 3.75/1.66  tff(c_1054, plain, (~r2_hidden('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_32, c_1051])).
% 3.75/1.66  tff(c_1058, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_1054])).
% 3.75/1.66  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.75/1.66  
% 3.75/1.66  Inference rules
% 3.75/1.66  ----------------------
% 3.75/1.66  #Ref     : 0
% 3.75/1.66  #Sup     : 213
% 3.75/1.66  #Fact    : 0
% 3.75/1.66  #Define  : 0
% 3.75/1.66  #Split   : 3
% 3.75/1.66  #Chain   : 0
% 3.75/1.66  #Close   : 0
% 3.75/1.66  
% 3.75/1.66  Ordering : KBO
% 3.75/1.66  
% 3.75/1.66  Simplification rules
% 3.75/1.66  ----------------------
% 3.75/1.66  #Subsume      : 23
% 3.75/1.66  #Demod        : 132
% 3.75/1.66  #Tautology    : 30
% 3.75/1.66  #SimpNegUnit  : 0
% 3.75/1.66  #BackRed      : 0
% 3.75/1.66  
% 3.75/1.66  #Partial instantiations: 0
% 3.75/1.66  #Strategies tried      : 1
% 3.75/1.66  
% 3.75/1.66  Timing (in seconds)
% 3.75/1.66  ----------------------
% 3.75/1.67  Preprocessing        : 0.33
% 3.75/1.67  Parsing              : 0.18
% 3.75/1.67  CNF conversion       : 0.02
% 3.75/1.67  Main loop            : 0.51
% 3.75/1.67  Inferencing          : 0.20
% 3.75/1.67  Reduction            : 0.15
% 3.75/1.67  Demodulation         : 0.10
% 3.75/1.67  BG Simplification    : 0.03
% 3.75/1.67  Subsumption          : 0.11
% 3.75/1.67  Abstraction          : 0.03
% 3.75/1.67  MUC search           : 0.00
% 3.75/1.67  Cooper               : 0.00
% 3.75/1.67  Total                : 0.87
% 3.75/1.67  Index Insertion      : 0.00
% 3.75/1.67  Index Deletion       : 0.00
% 3.75/1.67  Index Matching       : 0.00
% 3.75/1.67  BG Taut test         : 0.00
%------------------------------------------------------------------------------
