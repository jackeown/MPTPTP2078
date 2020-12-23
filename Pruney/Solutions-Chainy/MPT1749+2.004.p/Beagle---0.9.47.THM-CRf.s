%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:50 EST 2020

% Result     : Theorem 10.82s
% Output     : CNFRefutation 11.11s
% Verified   : 
% Statistics : Number of formulae       :  200 (8869 expanded)
%              Number of leaves         :   44 (2945 expanded)
%              Depth                    :   39
%              Number of atoms          :  577 (58152 expanded)
%              Number of equality atoms :   56 (2968 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_funct_2 > v1_funct_2 > r2_hidden > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_funct_2 > k2_tmap_1 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(k2_partfun1,type,(
    k2_partfun1: ( $i * $i * $i * $i ) > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k2_tmap_1,type,(
    k2_tmap_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k3_funct_2,type,(
    k3_funct_2: ( $i * $i * $i * $i ) > $i )).

tff(r2_funct_2,type,(
    r2_funct_2: ( $i * $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_209,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & v2_pre_topc(B)
              & l1_pre_topc(B) )
           => ! [C] :
                ( ( ~ v2_struct_0(C)
                  & m1_pre_topc(C,B) )
               => ! [D] :
                    ( ( v1_funct_1(D)
                      & v1_funct_2(D,u1_struct_0(B),u1_struct_0(A))
                      & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B),u1_struct_0(A)))) )
                   => ! [E] :
                        ( ( v1_funct_1(E)
                          & v1_funct_2(E,u1_struct_0(C),u1_struct_0(A))
                          & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(A)))) )
                       => ( ! [F] :
                              ( m1_subset_1(F,u1_struct_0(B))
                             => ( r2_hidden(F,u1_struct_0(C))
                               => k3_funct_2(u1_struct_0(B),u1_struct_0(A),D,F) = k1_funct_1(E,F) ) )
                         => r2_funct_2(u1_struct_0(C),u1_struct_0(A),k2_tmap_1(B,A,D,C),E) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_tmap_1)).

tff(f_104,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_97,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_157,axiom,(
    ! [A,B,C,D] :
      ( ( l1_struct_0(A)
        & l1_struct_0(B)
        & v1_funct_1(C)
        & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B))))
        & l1_struct_0(D) )
     => ( v1_funct_1(k2_tmap_1(A,B,C,D))
        & v1_funct_2(k2_tmap_1(A,B,C,D),u1_struct_0(D),u1_struct_0(B))
        & m1_subset_1(k2_tmap_1(A,B,C,D),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D),u1_struct_0(B)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tmap_1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [D] :
          ( ( v1_funct_1(D)
            & v1_funct_2(D,A,B)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
         => ( r2_funct_2(A,B,C,D)
          <=> ! [E] :
                ( m1_subset_1(E,A)
               => k1_funct_1(C,E) = k1_funct_1(D,E) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_2)).

tff(f_31,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_164,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_112,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_93,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => k3_funct_2(A,B,C,D) = k1_funct_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

tff(f_46,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_80,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_139,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v2_pre_topc(B)
            & l1_pre_topc(B) )
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
             => ! [D] :
                  ( m1_pre_topc(D,A)
                 => k2_tmap_1(A,B,C,D) = k2_partfun1(u1_struct_0(A),u1_struct_0(B),C,u1_struct_0(D)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tmap_1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(A,B)
       => k1_funct_1(k7_relat_1(C,B),A) = k1_funct_1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_funct_1)).

tff(c_38,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_58,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_54,plain,(
    m1_pre_topc('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_72,plain,(
    ! [B_123,A_124] :
      ( l1_pre_topc(B_123)
      | ~ m1_pre_topc(B_123,A_124)
      | ~ l1_pre_topc(A_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_75,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_72])).

tff(c_78,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_75])).

tff(c_22,plain,(
    ! [A_34] :
      ( l1_struct_0(A_34)
      | ~ l1_pre_topc(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_64,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_52,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_50,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_48,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_205,plain,(
    ! [A_159,B_160,C_161,D_162] :
      ( v1_funct_1(k2_tmap_1(A_159,B_160,C_161,D_162))
      | ~ l1_struct_0(D_162)
      | ~ m1_subset_1(C_161,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_159),u1_struct_0(B_160))))
      | ~ v1_funct_2(C_161,u1_struct_0(A_159),u1_struct_0(B_160))
      | ~ v1_funct_1(C_161)
      | ~ l1_struct_0(B_160)
      | ~ l1_struct_0(A_159) ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_207,plain,(
    ! [D_162] :
      ( v1_funct_1(k2_tmap_1('#skF_3','#skF_2','#skF_5',D_162))
      | ~ l1_struct_0(D_162)
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_48,c_205])).

tff(c_212,plain,(
    ! [D_162] :
      ( v1_funct_1(k2_tmap_1('#skF_3','#skF_2','#skF_5',D_162))
      | ~ l1_struct_0(D_162)
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_207])).

tff(c_216,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_212])).

tff(c_219,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_216])).

tff(c_223,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_219])).

tff(c_224,plain,(
    ! [D_162] :
      ( ~ l1_struct_0('#skF_2')
      | v1_funct_1(k2_tmap_1('#skF_3','#skF_2','#skF_5',D_162))
      | ~ l1_struct_0(D_162) ) ),
    inference(splitRight,[status(thm)],[c_212])).

tff(c_237,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_224])).

tff(c_240,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_22,c_237])).

tff(c_244,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_240])).

tff(c_246,plain,(
    l1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_224])).

tff(c_46,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_44,plain,(
    v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_42,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_209,plain,(
    ! [D_162] :
      ( v1_funct_1(k2_tmap_1('#skF_4','#skF_2','#skF_6',D_162))
      | ~ l1_struct_0(D_162)
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_6')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_42,c_205])).

tff(c_215,plain,(
    ! [D_162] :
      ( v1_funct_1(k2_tmap_1('#skF_4','#skF_2','#skF_6',D_162))
      | ~ l1_struct_0(D_162)
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_209])).

tff(c_250,plain,(
    ! [D_162] :
      ( v1_funct_1(k2_tmap_1('#skF_4','#skF_2','#skF_6',D_162))
      | ~ l1_struct_0(D_162)
      | ~ l1_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_246,c_215])).

tff(c_251,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_250])).

tff(c_254,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_251])).

tff(c_258,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_254])).

tff(c_260,plain,(
    l1_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_250])).

tff(c_245,plain,(
    ! [D_162] :
      ( v1_funct_1(k2_tmap_1('#skF_3','#skF_2','#skF_5',D_162))
      | ~ l1_struct_0(D_162) ) ),
    inference(splitRight,[status(thm)],[c_224])).

tff(c_225,plain,(
    l1_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_212])).

tff(c_30,plain,(
    ! [A_54,B_55,C_56,D_57] :
      ( m1_subset_1(k2_tmap_1(A_54,B_55,C_56,D_57),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_57),u1_struct_0(B_55))))
      | ~ l1_struct_0(D_57)
      | ~ m1_subset_1(C_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_54),u1_struct_0(B_55))))
      | ~ v1_funct_2(C_56,u1_struct_0(A_54),u1_struct_0(B_55))
      | ~ v1_funct_1(C_56)
      | ~ l1_struct_0(B_55)
      | ~ l1_struct_0(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_307,plain,(
    ! [A_181,B_182,C_183,D_184] :
      ( m1_subset_1('#skF_1'(A_181,B_182,C_183,D_184),A_181)
      | r2_funct_2(A_181,B_182,C_183,D_184)
      | ~ m1_subset_1(D_184,k1_zfmisc_1(k2_zfmisc_1(A_181,B_182)))
      | ~ v1_funct_2(D_184,A_181,B_182)
      | ~ v1_funct_1(D_184)
      | ~ m1_subset_1(C_183,k1_zfmisc_1(k2_zfmisc_1(A_181,B_182)))
      | ~ v1_funct_2(C_183,A_181,B_182)
      | ~ v1_funct_1(C_183) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_313,plain,(
    ! [C_183] :
      ( m1_subset_1('#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),C_183,'#skF_6'),u1_struct_0('#skF_4'))
      | r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),C_183,'#skF_6')
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(C_183,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_183,u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_183) ) ),
    inference(resolution,[status(thm)],[c_42,c_307])).

tff(c_320,plain,(
    ! [C_183] :
      ( m1_subset_1('#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),C_183,'#skF_6'),u1_struct_0('#skF_4'))
      | r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),C_183,'#skF_6')
      | ~ m1_subset_1(C_183,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_183,u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_183) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_313])).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r2_hidden(A_1,B_2)
      | v1_xboole_0(B_2)
      | ~ m1_subset_1(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_102,plain,(
    ! [B_134,A_135] :
      ( m1_subset_1(u1_struct_0(B_134),k1_zfmisc_1(u1_struct_0(A_135)))
      | ~ m1_pre_topc(B_134,A_135)
      | ~ l1_pre_topc(A_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_4,plain,(
    ! [A_3,C_5,B_4] :
      ( m1_subset_1(A_3,C_5)
      | ~ m1_subset_1(B_4,k1_zfmisc_1(C_5))
      | ~ r2_hidden(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_120,plain,(
    ! [A_139,A_140,B_141] :
      ( m1_subset_1(A_139,u1_struct_0(A_140))
      | ~ r2_hidden(A_139,u1_struct_0(B_141))
      | ~ m1_pre_topc(B_141,A_140)
      | ~ l1_pre_topc(A_140) ) ),
    inference(resolution,[status(thm)],[c_102,c_4])).

tff(c_179,plain,(
    ! [A_155,A_156,B_157] :
      ( m1_subset_1(A_155,u1_struct_0(A_156))
      | ~ m1_pre_topc(B_157,A_156)
      | ~ l1_pre_topc(A_156)
      | v1_xboole_0(u1_struct_0(B_157))
      | ~ m1_subset_1(A_155,u1_struct_0(B_157)) ) ),
    inference(resolution,[status(thm)],[c_2,c_120])).

tff(c_181,plain,(
    ! [A_155] :
      ( m1_subset_1(A_155,u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | ~ m1_subset_1(A_155,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_54,c_179])).

tff(c_184,plain,(
    ! [A_155] :
      ( m1_subset_1(A_155,u1_struct_0('#skF_3'))
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | ~ m1_subset_1(A_155,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_181])).

tff(c_185,plain,(
    v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_184])).

tff(c_26,plain,(
    ! [A_38] :
      ( ~ v1_xboole_0(u1_struct_0(A_38))
      | ~ l1_struct_0(A_38)
      | v2_struct_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_188,plain,
    ( ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_185,c_26])).

tff(c_191,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_188])).

tff(c_194,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_191])).

tff(c_198,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_194])).

tff(c_199,plain,(
    ! [A_155] :
      ( m1_subset_1(A_155,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(A_155,u1_struct_0('#skF_4')) ) ),
    inference(splitRight,[status(thm)],[c_184])).

tff(c_200,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_184])).

tff(c_62,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_201,plain,(
    ! [A_158] :
      ( m1_subset_1(A_158,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(A_158,u1_struct_0('#skF_4')) ) ),
    inference(splitRight,[status(thm)],[c_184])).

tff(c_20,plain,(
    ! [A_30,B_31,C_32,D_33] :
      ( k3_funct_2(A_30,B_31,C_32,D_33) = k1_funct_1(C_32,D_33)
      | ~ m1_subset_1(D_33,A_30)
      | ~ m1_subset_1(C_32,k1_zfmisc_1(k2_zfmisc_1(A_30,B_31)))
      | ~ v1_funct_2(C_32,A_30,B_31)
      | ~ v1_funct_1(C_32)
      | v1_xboole_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_204,plain,(
    ! [B_31,C_32,A_158] :
      ( k3_funct_2(u1_struct_0('#skF_3'),B_31,C_32,A_158) = k1_funct_1(C_32,A_158)
      | ~ m1_subset_1(C_32,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),B_31)))
      | ~ v1_funct_2(C_32,u1_struct_0('#skF_3'),B_31)
      | ~ v1_funct_1(C_32)
      | v1_xboole_0(u1_struct_0('#skF_3'))
      | ~ m1_subset_1(A_158,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_201,c_20])).

tff(c_321,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_204])).

tff(c_324,plain,
    ( ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_321,c_26])).

tff(c_327,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_225,c_324])).

tff(c_329,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_327])).

tff(c_338,plain,(
    ! [B_186,C_187,A_188] :
      ( k3_funct_2(u1_struct_0('#skF_3'),B_186,C_187,A_188) = k1_funct_1(C_187,A_188)
      | ~ m1_subset_1(C_187,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),B_186)))
      | ~ v1_funct_2(C_187,u1_struct_0('#skF_3'),B_186)
      | ~ v1_funct_1(C_187)
      | ~ m1_subset_1(A_188,u1_struct_0('#skF_4')) ) ),
    inference(splitRight,[status(thm)],[c_204])).

tff(c_343,plain,(
    ! [A_188] :
      ( k3_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_5',A_188) = k1_funct_1('#skF_5',A_188)
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(A_188,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_48,c_338])).

tff(c_350,plain,(
    ! [A_189] :
      ( k3_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_5',A_189) = k1_funct_1('#skF_5',A_189)
      | ~ m1_subset_1(A_189,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_343])).

tff(c_40,plain,(
    ! [F_118] :
      ( k3_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_5',F_118) = k1_funct_1('#skF_6',F_118)
      | ~ r2_hidden(F_118,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(F_118,u1_struct_0('#skF_3')) ) ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_365,plain,(
    ! [A_190] :
      ( k1_funct_1('#skF_5',A_190) = k1_funct_1('#skF_6',A_190)
      | ~ r2_hidden(A_190,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(A_190,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(A_190,u1_struct_0('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_350,c_40])).

tff(c_369,plain,(
    ! [A_1] :
      ( k1_funct_1('#skF_5',A_1) = k1_funct_1('#skF_6',A_1)
      | ~ m1_subset_1(A_1,u1_struct_0('#skF_3'))
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | ~ m1_subset_1(A_1,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_2,c_365])).

tff(c_373,plain,(
    ! [A_191] :
      ( k1_funct_1('#skF_5',A_191) = k1_funct_1('#skF_6',A_191)
      | ~ m1_subset_1(A_191,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(A_191,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_200,c_369])).

tff(c_378,plain,(
    ! [A_192] :
      ( k1_funct_1('#skF_5',A_192) = k1_funct_1('#skF_6',A_192)
      | ~ m1_subset_1(A_192,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_199,c_373])).

tff(c_451,plain,(
    ! [C_221] :
      ( k1_funct_1('#skF_5','#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),C_221,'#skF_6')) = k1_funct_1('#skF_6','#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),C_221,'#skF_6'))
      | r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),C_221,'#skF_6')
      | ~ m1_subset_1(C_221,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_221,u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_221) ) ),
    inference(resolution,[status(thm)],[c_320,c_378])).

tff(c_455,plain,(
    ! [A_54,C_56] :
      ( k1_funct_1('#skF_5','#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1(A_54,'#skF_2',C_56,'#skF_4'),'#skF_6')) = k1_funct_1('#skF_6','#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1(A_54,'#skF_2',C_56,'#skF_4'),'#skF_6'))
      | r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1(A_54,'#skF_2',C_56,'#skF_4'),'#skF_6')
      | ~ v1_funct_2(k2_tmap_1(A_54,'#skF_2',C_56,'#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1(A_54,'#skF_2',C_56,'#skF_4'))
      | ~ l1_struct_0('#skF_4')
      | ~ m1_subset_1(C_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_54),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_56,u1_struct_0(A_54),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_56)
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0(A_54) ) ),
    inference(resolution,[status(thm)],[c_30,c_451])).

tff(c_901,plain,(
    ! [A_396,C_397] :
      ( k1_funct_1('#skF_5','#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1(A_396,'#skF_2',C_397,'#skF_4'),'#skF_6')) = k1_funct_1('#skF_6','#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1(A_396,'#skF_2',C_397,'#skF_4'),'#skF_6'))
      | r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1(A_396,'#skF_2',C_397,'#skF_4'),'#skF_6')
      | ~ v1_funct_2(k2_tmap_1(A_396,'#skF_2',C_397,'#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1(A_396,'#skF_2',C_397,'#skF_4'))
      | ~ m1_subset_1(C_397,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_396),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_397,u1_struct_0(A_396),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_397)
      | ~ l1_struct_0(A_396) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_246,c_260,c_455])).

tff(c_908,plain,
    ( k1_funct_1('#skF_5','#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4'),'#skF_6')) = k1_funct_1('#skF_6','#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4'),'#skF_6'))
    | r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4'),'#skF_6')
    | ~ v1_funct_2(k2_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4'))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_5')
    | ~ l1_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_901])).

tff(c_917,plain,
    ( k1_funct_1('#skF_5','#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4'),'#skF_6')) = k1_funct_1('#skF_6','#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4'),'#skF_6'))
    | r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4'),'#skF_6')
    | ~ v1_funct_2(k2_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_225,c_52,c_50,c_908])).

tff(c_918,plain,
    ( k1_funct_1('#skF_5','#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4'),'#skF_6')) = k1_funct_1('#skF_6','#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4'),'#skF_6'))
    | ~ v1_funct_2(k2_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_917])).

tff(c_938,plain,(
    ~ v1_funct_1(k2_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_918])).

tff(c_941,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_245,c_938])).

tff(c_945,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_260,c_941])).

tff(c_947,plain,(
    v1_funct_1(k2_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_918])).

tff(c_226,plain,(
    ! [A_163,B_164,C_165,D_166] :
      ( v1_funct_2(k2_tmap_1(A_163,B_164,C_165,D_166),u1_struct_0(D_166),u1_struct_0(B_164))
      | ~ l1_struct_0(D_166)
      | ~ m1_subset_1(C_165,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_163),u1_struct_0(B_164))))
      | ~ v1_funct_2(C_165,u1_struct_0(A_163),u1_struct_0(B_164))
      | ~ v1_funct_1(C_165)
      | ~ l1_struct_0(B_164)
      | ~ l1_struct_0(A_163) ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_228,plain,(
    ! [D_166] :
      ( v1_funct_2(k2_tmap_1('#skF_3','#skF_2','#skF_5',D_166),u1_struct_0(D_166),u1_struct_0('#skF_2'))
      | ~ l1_struct_0(D_166)
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_48,c_226])).

tff(c_233,plain,(
    ! [D_166] :
      ( v1_funct_2(k2_tmap_1('#skF_3','#skF_2','#skF_5',D_166),u1_struct_0(D_166),u1_struct_0('#skF_2'))
      | ~ l1_struct_0(D_166)
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_228])).

tff(c_289,plain,(
    ! [D_166] :
      ( v1_funct_2(k2_tmap_1('#skF_3','#skF_2','#skF_5',D_166),u1_struct_0(D_166),u1_struct_0('#skF_2'))
      | ~ l1_struct_0(D_166) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_225,c_246,c_233])).

tff(c_946,plain,
    ( ~ v1_funct_2(k2_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | k1_funct_1('#skF_5','#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4'),'#skF_6')) = k1_funct_1('#skF_6','#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4'),'#skF_6')) ),
    inference(splitRight,[status(thm)],[c_918])).

tff(c_964,plain,(
    ~ v1_funct_2(k2_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_946])).

tff(c_967,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_289,c_964])).

tff(c_971,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_260,c_967])).

tff(c_973,plain,(
    v1_funct_2(k2_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_946])).

tff(c_259,plain,(
    ! [D_162] :
      ( v1_funct_1(k2_tmap_1('#skF_4','#skF_2','#skF_6',D_162))
      | ~ l1_struct_0(D_162) ) ),
    inference(splitRight,[status(thm)],[c_250])).

tff(c_911,plain,
    ( k1_funct_1('#skF_5','#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_4'),'#skF_6')) = k1_funct_1('#skF_6','#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_4'),'#skF_6'))
    | r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_4'),'#skF_6')
    | ~ v1_funct_2(k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_4'))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_6')
    | ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_901])).

tff(c_921,plain,
    ( k1_funct_1('#skF_5','#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_4'),'#skF_6')) = k1_funct_1('#skF_6','#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_4'),'#skF_6'))
    | r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_4'),'#skF_6')
    | ~ v1_funct_2(k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_260,c_46,c_44,c_911])).

tff(c_1402,plain,(
    ~ v1_funct_1(k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_921])).

tff(c_1405,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_259,c_1402])).

tff(c_1409,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_260,c_1405])).

tff(c_1411,plain,(
    v1_funct_1(k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_921])).

tff(c_230,plain,(
    ! [D_166] :
      ( v1_funct_2(k2_tmap_1('#skF_4','#skF_2','#skF_6',D_166),u1_struct_0(D_166),u1_struct_0('#skF_2'))
      | ~ l1_struct_0(D_166)
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_6')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_42,c_226])).

tff(c_236,plain,(
    ! [D_166] :
      ( v1_funct_2(k2_tmap_1('#skF_4','#skF_2','#skF_6',D_166),u1_struct_0(D_166),u1_struct_0('#skF_2'))
      | ~ l1_struct_0(D_166)
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_230])).

tff(c_285,plain,(
    ! [D_166] :
      ( v1_funct_2(k2_tmap_1('#skF_4','#skF_2','#skF_6',D_166),u1_struct_0(D_166),u1_struct_0('#skF_2'))
      | ~ l1_struct_0(D_166) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_260,c_246,c_236])).

tff(c_1410,plain,
    ( ~ v1_funct_2(k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_4'),'#skF_6')
    | k1_funct_1('#skF_5','#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_4'),'#skF_6')) = k1_funct_1('#skF_6','#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_4'),'#skF_6')) ),
    inference(splitRight,[status(thm)],[c_921])).

tff(c_1412,plain,(
    ~ v1_funct_2(k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_1410])).

tff(c_1415,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_285,c_1412])).

tff(c_1419,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_260,c_1415])).

tff(c_1421,plain,(
    v1_funct_2(k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_1410])).

tff(c_1420,plain,
    ( k1_funct_1('#skF_5','#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_4'),'#skF_6')) = k1_funct_1('#skF_6','#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_4'),'#skF_6'))
    | r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_4'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_1410])).

tff(c_1472,plain,(
    r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_4'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_1420])).

tff(c_383,plain,(
    ! [C_193,B_194,E_195,A_196,D_197] :
      ( k1_funct_1(D_197,E_195) = k1_funct_1(C_193,E_195)
      | ~ m1_subset_1(E_195,A_196)
      | ~ r2_funct_2(A_196,B_194,C_193,D_197)
      | ~ m1_subset_1(D_197,k1_zfmisc_1(k2_zfmisc_1(A_196,B_194)))
      | ~ v1_funct_2(D_197,A_196,B_194)
      | ~ v1_funct_1(D_197)
      | ~ m1_subset_1(C_193,k1_zfmisc_1(k2_zfmisc_1(A_196,B_194)))
      | ~ v1_funct_2(C_193,A_196,B_194)
      | ~ v1_funct_1(C_193) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_400,plain,(
    ! [D_197,C_183,C_193,B_194] :
      ( k1_funct_1(D_197,'#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),C_183,'#skF_6')) = k1_funct_1(C_193,'#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),C_183,'#skF_6'))
      | ~ r2_funct_2(u1_struct_0('#skF_4'),B_194,C_193,D_197)
      | ~ m1_subset_1(D_197,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),B_194)))
      | ~ v1_funct_2(D_197,u1_struct_0('#skF_4'),B_194)
      | ~ v1_funct_1(D_197)
      | ~ m1_subset_1(C_193,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),B_194)))
      | ~ v1_funct_2(C_193,u1_struct_0('#skF_4'),B_194)
      | ~ v1_funct_1(C_193)
      | r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),C_183,'#skF_6')
      | ~ m1_subset_1(C_183,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_183,u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_183) ) ),
    inference(resolution,[status(thm)],[c_320,c_383])).

tff(c_1474,plain,(
    ! [C_183] :
      ( k1_funct_1(k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_4'),'#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),C_183,'#skF_6')) = k1_funct_1('#skF_6','#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),C_183,'#skF_6'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_4'))
      | r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),C_183,'#skF_6')
      | ~ m1_subset_1(C_183,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_183,u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_183) ) ),
    inference(resolution,[status(thm)],[c_1472,c_400])).

tff(c_1477,plain,(
    ! [C_183] :
      ( k1_funct_1(k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_4'),'#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),C_183,'#skF_6')) = k1_funct_1('#skF_6','#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),C_183,'#skF_6'))
      | ~ m1_subset_1(k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
      | r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),C_183,'#skF_6')
      | ~ m1_subset_1(C_183,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_183,u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_183) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1411,c_1421,c_46,c_44,c_42,c_1474])).

tff(c_2270,plain,(
    ~ m1_subset_1(k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_1477])).

tff(c_2295,plain,
    ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_6')
    | ~ l1_struct_0('#skF_2')
    | ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_2270])).

tff(c_2299,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_260,c_246,c_46,c_44,c_42,c_2295])).

tff(c_2301,plain,(
    m1_subset_1(k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_1477])).

tff(c_16,plain,(
    ! [A_14,B_15,C_16,D_22] :
      ( m1_subset_1('#skF_1'(A_14,B_15,C_16,D_22),A_14)
      | r2_funct_2(A_14,B_15,C_16,D_22)
      | ~ m1_subset_1(D_22,k1_zfmisc_1(k2_zfmisc_1(A_14,B_15)))
      | ~ v1_funct_2(D_22,A_14,B_15)
      | ~ v1_funct_1(D_22)
      | ~ m1_subset_1(C_16,k1_zfmisc_1(k2_zfmisc_1(A_14,B_15)))
      | ~ v1_funct_2(C_16,A_14,B_15)
      | ~ v1_funct_1(C_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_2328,plain,(
    ! [C_16] :
      ( m1_subset_1('#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),C_16,k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_4')),u1_struct_0('#skF_4'))
      | r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),C_16,k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_4'))
      | ~ v1_funct_2(k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_4'))
      | ~ m1_subset_1(C_16,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_16,u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_16) ) ),
    inference(resolution,[status(thm)],[c_2301,c_16])).

tff(c_2635,plain,(
    ! [C_617] :
      ( m1_subset_1('#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),C_617,k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_4')),u1_struct_0('#skF_4'))
      | r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),C_617,k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_4'))
      | ~ m1_subset_1(C_617,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_617,u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_617) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1411,c_1421,c_2328])).

tff(c_8,plain,(
    ! [A_9,B_10] : v1_relat_1(k2_zfmisc_1(A_9,B_10)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_6,plain,(
    ! [B_8,A_6] :
      ( v1_relat_1(B_8)
      | ~ m1_subset_1(B_8,k1_zfmisc_1(A_6))
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_88,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_48,c_6])).

tff(c_91,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_88])).

tff(c_68,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_60,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_66,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_134,plain,(
    ! [A_145,B_146,C_147,D_148] :
      ( k2_partfun1(A_145,B_146,C_147,D_148) = k7_relat_1(C_147,D_148)
      | ~ m1_subset_1(C_147,k1_zfmisc_1(k2_zfmisc_1(A_145,B_146)))
      | ~ v1_funct_1(C_147) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_136,plain,(
    ! [D_148] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_5',D_148) = k7_relat_1('#skF_5',D_148)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_48,c_134])).

tff(c_141,plain,(
    ! [D_148] : k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_5',D_148) = k7_relat_1('#skF_5',D_148) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_136])).

tff(c_493,plain,(
    ! [A_231,B_232,C_233,D_234] :
      ( k2_partfun1(u1_struct_0(A_231),u1_struct_0(B_232),C_233,u1_struct_0(D_234)) = k2_tmap_1(A_231,B_232,C_233,D_234)
      | ~ m1_pre_topc(D_234,A_231)
      | ~ m1_subset_1(C_233,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_231),u1_struct_0(B_232))))
      | ~ v1_funct_2(C_233,u1_struct_0(A_231),u1_struct_0(B_232))
      | ~ v1_funct_1(C_233)
      | ~ l1_pre_topc(B_232)
      | ~ v2_pre_topc(B_232)
      | v2_struct_0(B_232)
      | ~ l1_pre_topc(A_231)
      | ~ v2_pre_topc(A_231)
      | v2_struct_0(A_231) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_497,plain,(
    ! [D_234] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_234)) = k2_tmap_1('#skF_3','#skF_2','#skF_5',D_234)
      | ~ m1_pre_topc(D_234,'#skF_3')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_48,c_493])).

tff(c_503,plain,(
    ! [D_234] :
      ( k7_relat_1('#skF_5',u1_struct_0(D_234)) = k2_tmap_1('#skF_3','#skF_2','#skF_5',D_234)
      | ~ m1_pre_topc(D_234,'#skF_3')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_66,c_64,c_52,c_50,c_141,c_497])).

tff(c_509,plain,(
    ! [D_235] :
      ( k7_relat_1('#skF_5',u1_struct_0(D_235)) = k2_tmap_1('#skF_3','#skF_2','#skF_5',D_235)
      | ~ m1_pre_topc(D_235,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_68,c_503])).

tff(c_10,plain,(
    ! [C_13,B_12,A_11] :
      ( k1_funct_1(k7_relat_1(C_13,B_12),A_11) = k1_funct_1(C_13,A_11)
      | ~ r2_hidden(A_11,B_12)
      | ~ v1_funct_1(C_13)
      | ~ v1_relat_1(C_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_515,plain,(
    ! [D_235,A_11] :
      ( k1_funct_1(k2_tmap_1('#skF_3','#skF_2','#skF_5',D_235),A_11) = k1_funct_1('#skF_5',A_11)
      | ~ r2_hidden(A_11,u1_struct_0(D_235))
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5')
      | ~ m1_pre_topc(D_235,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_509,c_10])).

tff(c_524,plain,(
    ! [D_236,A_237] :
      ( k1_funct_1(k2_tmap_1('#skF_3','#skF_2','#skF_5',D_236),A_237) = k1_funct_1('#skF_5',A_237)
      | ~ r2_hidden(A_237,u1_struct_0(D_236))
      | ~ m1_pre_topc(D_236,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_52,c_515])).

tff(c_529,plain,(
    ! [D_236,A_1] :
      ( k1_funct_1(k2_tmap_1('#skF_3','#skF_2','#skF_5',D_236),A_1) = k1_funct_1('#skF_5',A_1)
      | ~ m1_pre_topc(D_236,'#skF_3')
      | v1_xboole_0(u1_struct_0(D_236))
      | ~ m1_subset_1(A_1,u1_struct_0(D_236)) ) ),
    inference(resolution,[status(thm)],[c_2,c_524])).

tff(c_2638,plain,(
    ! [C_617] :
      ( k1_funct_1(k2_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4'),'#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),C_617,k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_4'))) = k1_funct_1('#skF_5','#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),C_617,k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_4')))
      | ~ m1_pre_topc('#skF_4','#skF_3')
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),C_617,k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_4'))
      | ~ m1_subset_1(C_617,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_617,u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_617) ) ),
    inference(resolution,[status(thm)],[c_2635,c_529])).

tff(c_2648,plain,(
    ! [C_617] :
      ( k1_funct_1(k2_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4'),'#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),C_617,k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_4'))) = k1_funct_1('#skF_5','#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),C_617,k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_4')))
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),C_617,k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_4'))
      | ~ m1_subset_1(C_617,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_617,u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_617) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_2638])).

tff(c_2824,plain,(
    ! [C_633] :
      ( k1_funct_1(k2_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4'),'#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),C_633,k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_4'))) = k1_funct_1('#skF_5','#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),C_633,k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_4')))
      | r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),C_633,k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_4'))
      | ~ m1_subset_1(C_633,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_633,u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_633) ) ),
    inference(negUnitSimplification,[status(thm)],[c_200,c_2648])).

tff(c_14,plain,(
    ! [D_22,A_14,B_15,C_16] :
      ( k1_funct_1(D_22,'#skF_1'(A_14,B_15,C_16,D_22)) != k1_funct_1(C_16,'#skF_1'(A_14,B_15,C_16,D_22))
      | r2_funct_2(A_14,B_15,C_16,D_22)
      | ~ m1_subset_1(D_22,k1_zfmisc_1(k2_zfmisc_1(A_14,B_15)))
      | ~ v1_funct_2(D_22,A_14,B_15)
      | ~ v1_funct_1(D_22)
      | ~ m1_subset_1(C_16,k1_zfmisc_1(k2_zfmisc_1(A_14,B_15)))
      | ~ v1_funct_2(C_16,A_14,B_15)
      | ~ v1_funct_1(C_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_2833,plain,
    ( k1_funct_1(k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_4'),'#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4'),k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_4'))) != k1_funct_1('#skF_5','#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4'),k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_4')))
    | r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4'),k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_4'))
    | ~ m1_subset_1(k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_4'))
    | ~ m1_subset_1(k2_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k2_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4'))
    | r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4'),k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_4'))
    | ~ m1_subset_1(k2_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k2_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2824,c_14])).

tff(c_2841,plain,
    ( k1_funct_1(k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_4'),'#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4'),k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_4'))) != k1_funct_1('#skF_5','#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4'),k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_4')))
    | r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4'),k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_4'))
    | ~ m1_subset_1(k2_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_947,c_973,c_947,c_973,c_1411,c_1421,c_2301,c_2833])).

tff(c_4706,plain,(
    ~ m1_subset_1(k2_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_2841])).

tff(c_4709,plain,
    ( ~ l1_struct_0('#skF_4')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_5')
    | ~ l1_struct_0('#skF_2')
    | ~ l1_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_4706])).

tff(c_4713,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_225,c_246,c_52,c_50,c_48,c_260,c_4709])).

tff(c_4715,plain,(
    m1_subset_1(k2_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_2841])).

tff(c_972,plain,(
    k1_funct_1('#skF_5','#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4'),'#skF_6')) = k1_funct_1('#skF_6','#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4'),'#skF_6')) ),
    inference(splitRight,[status(thm)],[c_946])).

tff(c_531,plain,(
    ! [D_242,A_243] :
      ( k1_funct_1(k2_tmap_1('#skF_3','#skF_2','#skF_5',D_242),A_243) = k1_funct_1('#skF_5',A_243)
      | ~ m1_pre_topc(D_242,'#skF_3')
      | v1_xboole_0(u1_struct_0(D_242))
      | ~ m1_subset_1(A_243,u1_struct_0(D_242)) ) ),
    inference(resolution,[status(thm)],[c_2,c_524])).

tff(c_537,plain,(
    ! [C_183] :
      ( k1_funct_1(k2_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4'),'#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),C_183,'#skF_6')) = k1_funct_1('#skF_5','#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),C_183,'#skF_6'))
      | ~ m1_pre_topc('#skF_4','#skF_3')
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),C_183,'#skF_6')
      | ~ m1_subset_1(C_183,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_183,u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_183) ) ),
    inference(resolution,[status(thm)],[c_320,c_531])).

tff(c_546,plain,(
    ! [C_183] :
      ( k1_funct_1(k2_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4'),'#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),C_183,'#skF_6')) = k1_funct_1('#skF_5','#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),C_183,'#skF_6'))
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),C_183,'#skF_6')
      | ~ m1_subset_1(C_183,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_183,u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_183) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_537])).

tff(c_547,plain,(
    ! [C_183] :
      ( k1_funct_1(k2_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4'),'#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),C_183,'#skF_6')) = k1_funct_1('#skF_5','#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),C_183,'#skF_6'))
      | r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),C_183,'#skF_6')
      | ~ m1_subset_1(C_183,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_183,u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_183) ) ),
    inference(negUnitSimplification,[status(thm)],[c_200,c_546])).

tff(c_4754,plain,
    ( k1_funct_1(k2_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4'),'#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4'),'#skF_6')) = k1_funct_1('#skF_5','#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4'),'#skF_6'))
    | r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4'),'#skF_6')
    | ~ v1_funct_2(k2_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4')) ),
    inference(resolution,[status(thm)],[c_4715,c_547])).

tff(c_4812,plain,
    ( k1_funct_1(k2_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4'),'#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4'),'#skF_6')) = k1_funct_1('#skF_6','#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4'),'#skF_6'))
    | r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_947,c_973,c_972,c_4754])).

tff(c_4813,plain,(
    k1_funct_1(k2_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4'),'#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4'),'#skF_6')) = k1_funct_1('#skF_6','#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4'),'#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_4812])).

tff(c_4860,plain,
    ( r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4'),'#skF_6')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1(k2_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k2_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4813,c_14])).

tff(c_4865,plain,(
    r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_947,c_973,c_4715,c_46,c_44,c_42,c_4860])).

tff(c_4867,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_4865])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n016.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:32:04 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.82/4.12  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.97/4.14  
% 10.97/4.14  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.97/4.14  %$ r2_funct_2 > v1_funct_2 > r2_hidden > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_funct_2 > k2_tmap_1 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 10.97/4.14  
% 10.97/4.14  %Foreground sorts:
% 10.97/4.14  
% 10.97/4.14  
% 10.97/4.14  %Background operators:
% 10.97/4.14  
% 10.97/4.14  
% 10.97/4.14  %Foreground operators:
% 10.97/4.14  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 10.97/4.14  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 10.97/4.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.97/4.14  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.97/4.14  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 10.97/4.14  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 10.97/4.14  tff('#skF_5', type, '#skF_5': $i).
% 10.97/4.14  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 10.97/4.14  tff('#skF_6', type, '#skF_6': $i).
% 10.97/4.14  tff('#skF_2', type, '#skF_2': $i).
% 10.97/4.14  tff('#skF_3', type, '#skF_3': $i).
% 10.97/4.14  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.97/4.14  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 10.97/4.14  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 10.97/4.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.97/4.14  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 10.97/4.14  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 10.97/4.14  tff('#skF_4', type, '#skF_4': $i).
% 10.97/4.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.97/4.14  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 10.97/4.14  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 10.97/4.14  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 10.97/4.14  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 10.97/4.14  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 10.97/4.14  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 10.97/4.14  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 10.97/4.14  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 10.97/4.14  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 10.97/4.14  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.97/4.14  
% 11.11/4.17  tff(f_209, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, B)) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(A))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(A))))) => ((![F]: (m1_subset_1(F, u1_struct_0(B)) => (r2_hidden(F, u1_struct_0(C)) => (k3_funct_2(u1_struct_0(B), u1_struct_0(A), D, F) = k1_funct_1(E, F))))) => r2_funct_2(u1_struct_0(C), u1_struct_0(A), k2_tmap_1(B, A, D, C), E)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_tmap_1)).
% 11.11/4.17  tff(f_104, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 11.11/4.17  tff(f_97, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 11.11/4.17  tff(f_157, axiom, (![A, B, C, D]: ((((((l1_struct_0(A) & l1_struct_0(B)) & v1_funct_1(C)) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) & l1_struct_0(D)) => ((v1_funct_1(k2_tmap_1(A, B, C, D)) & v1_funct_2(k2_tmap_1(A, B, C, D), u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(k2_tmap_1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tmap_1)).
% 11.11/4.17  tff(f_74, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_funct_2(A, B, C, D) <=> (![E]: (m1_subset_1(E, A) => (k1_funct_1(C, E) = k1_funct_1(D, E))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_funct_2)).
% 11.11/4.17  tff(f_31, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 11.11/4.17  tff(f_164, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 11.11/4.17  tff(f_37, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 11.11/4.17  tff(f_112, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 11.11/4.17  tff(f_93, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => (k3_funct_2(A, B, C, D) = k1_funct_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 11.11/4.17  tff(f_46, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 11.11/4.17  tff(f_44, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 11.11/4.17  tff(f_80, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 11.11/4.17  tff(f_139, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tmap_1)).
% 11.11/4.17  tff(f_54, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, B) => (k1_funct_1(k7_relat_1(C, B), A) = k1_funct_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_funct_1)).
% 11.11/4.17  tff(c_38, plain, (~r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_209])).
% 11.11/4.17  tff(c_58, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_209])).
% 11.11/4.17  tff(c_54, plain, (m1_pre_topc('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_209])).
% 11.11/4.17  tff(c_72, plain, (![B_123, A_124]: (l1_pre_topc(B_123) | ~m1_pre_topc(B_123, A_124) | ~l1_pre_topc(A_124))), inference(cnfTransformation, [status(thm)], [f_104])).
% 11.11/4.17  tff(c_75, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_54, c_72])).
% 11.11/4.17  tff(c_78, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_75])).
% 11.11/4.17  tff(c_22, plain, (![A_34]: (l1_struct_0(A_34) | ~l1_pre_topc(A_34))), inference(cnfTransformation, [status(thm)], [f_97])).
% 11.11/4.17  tff(c_64, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_209])).
% 11.11/4.17  tff(c_52, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_209])).
% 11.11/4.17  tff(c_50, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_209])).
% 11.11/4.17  tff(c_48, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_209])).
% 11.11/4.17  tff(c_205, plain, (![A_159, B_160, C_161, D_162]: (v1_funct_1(k2_tmap_1(A_159, B_160, C_161, D_162)) | ~l1_struct_0(D_162) | ~m1_subset_1(C_161, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_159), u1_struct_0(B_160)))) | ~v1_funct_2(C_161, u1_struct_0(A_159), u1_struct_0(B_160)) | ~v1_funct_1(C_161) | ~l1_struct_0(B_160) | ~l1_struct_0(A_159))), inference(cnfTransformation, [status(thm)], [f_157])).
% 11.11/4.17  tff(c_207, plain, (![D_162]: (v1_funct_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_5', D_162)) | ~l1_struct_0(D_162) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_48, c_205])).
% 11.11/4.17  tff(c_212, plain, (![D_162]: (v1_funct_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_5', D_162)) | ~l1_struct_0(D_162) | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_207])).
% 11.11/4.17  tff(c_216, plain, (~l1_struct_0('#skF_3')), inference(splitLeft, [status(thm)], [c_212])).
% 11.11/4.17  tff(c_219, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_22, c_216])).
% 11.11/4.17  tff(c_223, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_219])).
% 11.11/4.17  tff(c_224, plain, (![D_162]: (~l1_struct_0('#skF_2') | v1_funct_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_5', D_162)) | ~l1_struct_0(D_162))), inference(splitRight, [status(thm)], [c_212])).
% 11.11/4.17  tff(c_237, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_224])).
% 11.11/4.17  tff(c_240, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_22, c_237])).
% 11.11/4.17  tff(c_244, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_240])).
% 11.11/4.17  tff(c_246, plain, (l1_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_224])).
% 11.11/4.17  tff(c_46, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_209])).
% 11.11/4.17  tff(c_44, plain, (v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_209])).
% 11.11/4.17  tff(c_42, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_209])).
% 11.11/4.17  tff(c_209, plain, (![D_162]: (v1_funct_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_6', D_162)) | ~l1_struct_0(D_162) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_42, c_205])).
% 11.11/4.17  tff(c_215, plain, (![D_162]: (v1_funct_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_6', D_162)) | ~l1_struct_0(D_162) | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_209])).
% 11.11/4.17  tff(c_250, plain, (![D_162]: (v1_funct_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_6', D_162)) | ~l1_struct_0(D_162) | ~l1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_246, c_215])).
% 11.11/4.17  tff(c_251, plain, (~l1_struct_0('#skF_4')), inference(splitLeft, [status(thm)], [c_250])).
% 11.11/4.17  tff(c_254, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_22, c_251])).
% 11.11/4.17  tff(c_258, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_78, c_254])).
% 11.11/4.17  tff(c_260, plain, (l1_struct_0('#skF_4')), inference(splitRight, [status(thm)], [c_250])).
% 11.11/4.17  tff(c_245, plain, (![D_162]: (v1_funct_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_5', D_162)) | ~l1_struct_0(D_162))), inference(splitRight, [status(thm)], [c_224])).
% 11.11/4.17  tff(c_225, plain, (l1_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_212])).
% 11.11/4.17  tff(c_30, plain, (![A_54, B_55, C_56, D_57]: (m1_subset_1(k2_tmap_1(A_54, B_55, C_56, D_57), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_57), u1_struct_0(B_55)))) | ~l1_struct_0(D_57) | ~m1_subset_1(C_56, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_54), u1_struct_0(B_55)))) | ~v1_funct_2(C_56, u1_struct_0(A_54), u1_struct_0(B_55)) | ~v1_funct_1(C_56) | ~l1_struct_0(B_55) | ~l1_struct_0(A_54))), inference(cnfTransformation, [status(thm)], [f_157])).
% 11.11/4.17  tff(c_307, plain, (![A_181, B_182, C_183, D_184]: (m1_subset_1('#skF_1'(A_181, B_182, C_183, D_184), A_181) | r2_funct_2(A_181, B_182, C_183, D_184) | ~m1_subset_1(D_184, k1_zfmisc_1(k2_zfmisc_1(A_181, B_182))) | ~v1_funct_2(D_184, A_181, B_182) | ~v1_funct_1(D_184) | ~m1_subset_1(C_183, k1_zfmisc_1(k2_zfmisc_1(A_181, B_182))) | ~v1_funct_2(C_183, A_181, B_182) | ~v1_funct_1(C_183))), inference(cnfTransformation, [status(thm)], [f_74])).
% 11.11/4.17  tff(c_313, plain, (![C_183]: (m1_subset_1('#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), C_183, '#skF_6'), u1_struct_0('#skF_4')) | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), C_183, '#skF_6') | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~m1_subset_1(C_183, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2(C_183, u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(C_183))), inference(resolution, [status(thm)], [c_42, c_307])).
% 11.11/4.17  tff(c_320, plain, (![C_183]: (m1_subset_1('#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), C_183, '#skF_6'), u1_struct_0('#skF_4')) | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), C_183, '#skF_6') | ~m1_subset_1(C_183, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2(C_183, u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(C_183))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_313])).
% 11.11/4.17  tff(c_56, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_209])).
% 11.11/4.17  tff(c_2, plain, (![A_1, B_2]: (r2_hidden(A_1, B_2) | v1_xboole_0(B_2) | ~m1_subset_1(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.11/4.17  tff(c_102, plain, (![B_134, A_135]: (m1_subset_1(u1_struct_0(B_134), k1_zfmisc_1(u1_struct_0(A_135))) | ~m1_pre_topc(B_134, A_135) | ~l1_pre_topc(A_135))), inference(cnfTransformation, [status(thm)], [f_164])).
% 11.11/4.17  tff(c_4, plain, (![A_3, C_5, B_4]: (m1_subset_1(A_3, C_5) | ~m1_subset_1(B_4, k1_zfmisc_1(C_5)) | ~r2_hidden(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 11.11/4.17  tff(c_120, plain, (![A_139, A_140, B_141]: (m1_subset_1(A_139, u1_struct_0(A_140)) | ~r2_hidden(A_139, u1_struct_0(B_141)) | ~m1_pre_topc(B_141, A_140) | ~l1_pre_topc(A_140))), inference(resolution, [status(thm)], [c_102, c_4])).
% 11.11/4.17  tff(c_179, plain, (![A_155, A_156, B_157]: (m1_subset_1(A_155, u1_struct_0(A_156)) | ~m1_pre_topc(B_157, A_156) | ~l1_pre_topc(A_156) | v1_xboole_0(u1_struct_0(B_157)) | ~m1_subset_1(A_155, u1_struct_0(B_157)))), inference(resolution, [status(thm)], [c_2, c_120])).
% 11.11/4.17  tff(c_181, plain, (![A_155]: (m1_subset_1(A_155, u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | v1_xboole_0(u1_struct_0('#skF_4')) | ~m1_subset_1(A_155, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_54, c_179])).
% 11.11/4.17  tff(c_184, plain, (![A_155]: (m1_subset_1(A_155, u1_struct_0('#skF_3')) | v1_xboole_0(u1_struct_0('#skF_4')) | ~m1_subset_1(A_155, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_181])).
% 11.11/4.17  tff(c_185, plain, (v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_184])).
% 11.11/4.17  tff(c_26, plain, (![A_38]: (~v1_xboole_0(u1_struct_0(A_38)) | ~l1_struct_0(A_38) | v2_struct_0(A_38))), inference(cnfTransformation, [status(thm)], [f_112])).
% 11.11/4.17  tff(c_188, plain, (~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_185, c_26])).
% 11.11/4.17  tff(c_191, plain, (~l1_struct_0('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_56, c_188])).
% 11.11/4.17  tff(c_194, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_22, c_191])).
% 11.11/4.17  tff(c_198, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_78, c_194])).
% 11.11/4.17  tff(c_199, plain, (![A_155]: (m1_subset_1(A_155, u1_struct_0('#skF_3')) | ~m1_subset_1(A_155, u1_struct_0('#skF_4')))), inference(splitRight, [status(thm)], [c_184])).
% 11.11/4.17  tff(c_200, plain, (~v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_184])).
% 11.11/4.17  tff(c_62, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_209])).
% 11.11/4.17  tff(c_201, plain, (![A_158]: (m1_subset_1(A_158, u1_struct_0('#skF_3')) | ~m1_subset_1(A_158, u1_struct_0('#skF_4')))), inference(splitRight, [status(thm)], [c_184])).
% 11.11/4.17  tff(c_20, plain, (![A_30, B_31, C_32, D_33]: (k3_funct_2(A_30, B_31, C_32, D_33)=k1_funct_1(C_32, D_33) | ~m1_subset_1(D_33, A_30) | ~m1_subset_1(C_32, k1_zfmisc_1(k2_zfmisc_1(A_30, B_31))) | ~v1_funct_2(C_32, A_30, B_31) | ~v1_funct_1(C_32) | v1_xboole_0(A_30))), inference(cnfTransformation, [status(thm)], [f_93])).
% 11.11/4.17  tff(c_204, plain, (![B_31, C_32, A_158]: (k3_funct_2(u1_struct_0('#skF_3'), B_31, C_32, A_158)=k1_funct_1(C_32, A_158) | ~m1_subset_1(C_32, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), B_31))) | ~v1_funct_2(C_32, u1_struct_0('#skF_3'), B_31) | ~v1_funct_1(C_32) | v1_xboole_0(u1_struct_0('#skF_3')) | ~m1_subset_1(A_158, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_201, c_20])).
% 11.11/4.17  tff(c_321, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_204])).
% 11.11/4.17  tff(c_324, plain, (~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_321, c_26])).
% 11.11/4.17  tff(c_327, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_225, c_324])).
% 11.11/4.17  tff(c_329, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_327])).
% 11.11/4.17  tff(c_338, plain, (![B_186, C_187, A_188]: (k3_funct_2(u1_struct_0('#skF_3'), B_186, C_187, A_188)=k1_funct_1(C_187, A_188) | ~m1_subset_1(C_187, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), B_186))) | ~v1_funct_2(C_187, u1_struct_0('#skF_3'), B_186) | ~v1_funct_1(C_187) | ~m1_subset_1(A_188, u1_struct_0('#skF_4')))), inference(splitRight, [status(thm)], [c_204])).
% 11.11/4.17  tff(c_343, plain, (![A_188]: (k3_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_5', A_188)=k1_funct_1('#skF_5', A_188) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_subset_1(A_188, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_48, c_338])).
% 11.11/4.17  tff(c_350, plain, (![A_189]: (k3_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_5', A_189)=k1_funct_1('#skF_5', A_189) | ~m1_subset_1(A_189, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_343])).
% 11.11/4.17  tff(c_40, plain, (![F_118]: (k3_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_5', F_118)=k1_funct_1('#skF_6', F_118) | ~r2_hidden(F_118, u1_struct_0('#skF_4')) | ~m1_subset_1(F_118, u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_209])).
% 11.11/4.17  tff(c_365, plain, (![A_190]: (k1_funct_1('#skF_5', A_190)=k1_funct_1('#skF_6', A_190) | ~r2_hidden(A_190, u1_struct_0('#skF_4')) | ~m1_subset_1(A_190, u1_struct_0('#skF_3')) | ~m1_subset_1(A_190, u1_struct_0('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_350, c_40])).
% 11.11/4.17  tff(c_369, plain, (![A_1]: (k1_funct_1('#skF_5', A_1)=k1_funct_1('#skF_6', A_1) | ~m1_subset_1(A_1, u1_struct_0('#skF_3')) | v1_xboole_0(u1_struct_0('#skF_4')) | ~m1_subset_1(A_1, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_2, c_365])).
% 11.11/4.17  tff(c_373, plain, (![A_191]: (k1_funct_1('#skF_5', A_191)=k1_funct_1('#skF_6', A_191) | ~m1_subset_1(A_191, u1_struct_0('#skF_3')) | ~m1_subset_1(A_191, u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_200, c_369])).
% 11.11/4.17  tff(c_378, plain, (![A_192]: (k1_funct_1('#skF_5', A_192)=k1_funct_1('#skF_6', A_192) | ~m1_subset_1(A_192, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_199, c_373])).
% 11.11/4.17  tff(c_451, plain, (![C_221]: (k1_funct_1('#skF_5', '#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), C_221, '#skF_6'))=k1_funct_1('#skF_6', '#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), C_221, '#skF_6')) | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), C_221, '#skF_6') | ~m1_subset_1(C_221, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2(C_221, u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(C_221))), inference(resolution, [status(thm)], [c_320, c_378])).
% 11.11/4.17  tff(c_455, plain, (![A_54, C_56]: (k1_funct_1('#skF_5', '#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1(A_54, '#skF_2', C_56, '#skF_4'), '#skF_6'))=k1_funct_1('#skF_6', '#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1(A_54, '#skF_2', C_56, '#skF_4'), '#skF_6')) | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1(A_54, '#skF_2', C_56, '#skF_4'), '#skF_6') | ~v1_funct_2(k2_tmap_1(A_54, '#skF_2', C_56, '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1(A_54, '#skF_2', C_56, '#skF_4')) | ~l1_struct_0('#skF_4') | ~m1_subset_1(C_56, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_54), u1_struct_0('#skF_2')))) | ~v1_funct_2(C_56, u1_struct_0(A_54), u1_struct_0('#skF_2')) | ~v1_funct_1(C_56) | ~l1_struct_0('#skF_2') | ~l1_struct_0(A_54))), inference(resolution, [status(thm)], [c_30, c_451])).
% 11.11/4.17  tff(c_901, plain, (![A_396, C_397]: (k1_funct_1('#skF_5', '#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1(A_396, '#skF_2', C_397, '#skF_4'), '#skF_6'))=k1_funct_1('#skF_6', '#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1(A_396, '#skF_2', C_397, '#skF_4'), '#skF_6')) | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1(A_396, '#skF_2', C_397, '#skF_4'), '#skF_6') | ~v1_funct_2(k2_tmap_1(A_396, '#skF_2', C_397, '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1(A_396, '#skF_2', C_397, '#skF_4')) | ~m1_subset_1(C_397, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_396), u1_struct_0('#skF_2')))) | ~v1_funct_2(C_397, u1_struct_0(A_396), u1_struct_0('#skF_2')) | ~v1_funct_1(C_397) | ~l1_struct_0(A_396))), inference(demodulation, [status(thm), theory('equality')], [c_246, c_260, c_455])).
% 11.11/4.17  tff(c_908, plain, (k1_funct_1('#skF_5', '#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4'), '#skF_6'))=k1_funct_1('#skF_6', '#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4'), '#skF_6')) | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4'), '#skF_6') | ~v1_funct_2(k2_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4')) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_48, c_901])).
% 11.11/4.17  tff(c_917, plain, (k1_funct_1('#skF_5', '#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4'), '#skF_6'))=k1_funct_1('#skF_6', '#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4'), '#skF_6')) | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4'), '#skF_6') | ~v1_funct_2(k2_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_225, c_52, c_50, c_908])).
% 11.11/4.17  tff(c_918, plain, (k1_funct_1('#skF_5', '#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4'), '#skF_6'))=k1_funct_1('#skF_6', '#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4'), '#skF_6')) | ~v1_funct_2(k2_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_38, c_917])).
% 11.11/4.17  tff(c_938, plain, (~v1_funct_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4'))), inference(splitLeft, [status(thm)], [c_918])).
% 11.11/4.17  tff(c_941, plain, (~l1_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_245, c_938])).
% 11.11/4.17  tff(c_945, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_260, c_941])).
% 11.11/4.17  tff(c_947, plain, (v1_funct_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4'))), inference(splitRight, [status(thm)], [c_918])).
% 11.11/4.17  tff(c_226, plain, (![A_163, B_164, C_165, D_166]: (v1_funct_2(k2_tmap_1(A_163, B_164, C_165, D_166), u1_struct_0(D_166), u1_struct_0(B_164)) | ~l1_struct_0(D_166) | ~m1_subset_1(C_165, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_163), u1_struct_0(B_164)))) | ~v1_funct_2(C_165, u1_struct_0(A_163), u1_struct_0(B_164)) | ~v1_funct_1(C_165) | ~l1_struct_0(B_164) | ~l1_struct_0(A_163))), inference(cnfTransformation, [status(thm)], [f_157])).
% 11.11/4.17  tff(c_228, plain, (![D_166]: (v1_funct_2(k2_tmap_1('#skF_3', '#skF_2', '#skF_5', D_166), u1_struct_0(D_166), u1_struct_0('#skF_2')) | ~l1_struct_0(D_166) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_48, c_226])).
% 11.11/4.17  tff(c_233, plain, (![D_166]: (v1_funct_2(k2_tmap_1('#skF_3', '#skF_2', '#skF_5', D_166), u1_struct_0(D_166), u1_struct_0('#skF_2')) | ~l1_struct_0(D_166) | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_228])).
% 11.11/4.17  tff(c_289, plain, (![D_166]: (v1_funct_2(k2_tmap_1('#skF_3', '#skF_2', '#skF_5', D_166), u1_struct_0(D_166), u1_struct_0('#skF_2')) | ~l1_struct_0(D_166))), inference(demodulation, [status(thm), theory('equality')], [c_225, c_246, c_233])).
% 11.11/4.17  tff(c_946, plain, (~v1_funct_2(k2_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | k1_funct_1('#skF_5', '#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4'), '#skF_6'))=k1_funct_1('#skF_6', '#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4'), '#skF_6'))), inference(splitRight, [status(thm)], [c_918])).
% 11.11/4.17  tff(c_964, plain, (~v1_funct_2(k2_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_946])).
% 11.11/4.17  tff(c_967, plain, (~l1_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_289, c_964])).
% 11.11/4.17  tff(c_971, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_260, c_967])).
% 11.11/4.17  tff(c_973, plain, (v1_funct_2(k2_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_946])).
% 11.11/4.17  tff(c_259, plain, (![D_162]: (v1_funct_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_6', D_162)) | ~l1_struct_0(D_162))), inference(splitRight, [status(thm)], [c_250])).
% 11.11/4.17  tff(c_911, plain, (k1_funct_1('#skF_5', '#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_4'), '#skF_6'))=k1_funct_1('#skF_6', '#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_4'), '#skF_6')) | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_4'), '#skF_6') | ~v1_funct_2(k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_4')) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~l1_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_42, c_901])).
% 11.11/4.17  tff(c_921, plain, (k1_funct_1('#skF_5', '#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_4'), '#skF_6'))=k1_funct_1('#skF_6', '#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_4'), '#skF_6')) | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_4'), '#skF_6') | ~v1_funct_2(k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_260, c_46, c_44, c_911])).
% 11.11/4.17  tff(c_1402, plain, (~v1_funct_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_4'))), inference(splitLeft, [status(thm)], [c_921])).
% 11.11/4.17  tff(c_1405, plain, (~l1_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_259, c_1402])).
% 11.11/4.17  tff(c_1409, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_260, c_1405])).
% 11.11/4.17  tff(c_1411, plain, (v1_funct_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_4'))), inference(splitRight, [status(thm)], [c_921])).
% 11.11/4.17  tff(c_230, plain, (![D_166]: (v1_funct_2(k2_tmap_1('#skF_4', '#skF_2', '#skF_6', D_166), u1_struct_0(D_166), u1_struct_0('#skF_2')) | ~l1_struct_0(D_166) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_42, c_226])).
% 11.11/4.17  tff(c_236, plain, (![D_166]: (v1_funct_2(k2_tmap_1('#skF_4', '#skF_2', '#skF_6', D_166), u1_struct_0(D_166), u1_struct_0('#skF_2')) | ~l1_struct_0(D_166) | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_230])).
% 11.11/4.17  tff(c_285, plain, (![D_166]: (v1_funct_2(k2_tmap_1('#skF_4', '#skF_2', '#skF_6', D_166), u1_struct_0(D_166), u1_struct_0('#skF_2')) | ~l1_struct_0(D_166))), inference(demodulation, [status(thm), theory('equality')], [c_260, c_246, c_236])).
% 11.11/4.17  tff(c_1410, plain, (~v1_funct_2(k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_4'), '#skF_6') | k1_funct_1('#skF_5', '#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_4'), '#skF_6'))=k1_funct_1('#skF_6', '#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_4'), '#skF_6'))), inference(splitRight, [status(thm)], [c_921])).
% 11.11/4.17  tff(c_1412, plain, (~v1_funct_2(k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_1410])).
% 11.11/4.17  tff(c_1415, plain, (~l1_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_285, c_1412])).
% 11.11/4.17  tff(c_1419, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_260, c_1415])).
% 11.11/4.17  tff(c_1421, plain, (v1_funct_2(k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_1410])).
% 11.11/4.17  tff(c_1420, plain, (k1_funct_1('#skF_5', '#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_4'), '#skF_6'))=k1_funct_1('#skF_6', '#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_4'), '#skF_6')) | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_4'), '#skF_6')), inference(splitRight, [status(thm)], [c_1410])).
% 11.11/4.17  tff(c_1472, plain, (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_4'), '#skF_6')), inference(splitLeft, [status(thm)], [c_1420])).
% 11.11/4.17  tff(c_383, plain, (![C_193, B_194, E_195, A_196, D_197]: (k1_funct_1(D_197, E_195)=k1_funct_1(C_193, E_195) | ~m1_subset_1(E_195, A_196) | ~r2_funct_2(A_196, B_194, C_193, D_197) | ~m1_subset_1(D_197, k1_zfmisc_1(k2_zfmisc_1(A_196, B_194))) | ~v1_funct_2(D_197, A_196, B_194) | ~v1_funct_1(D_197) | ~m1_subset_1(C_193, k1_zfmisc_1(k2_zfmisc_1(A_196, B_194))) | ~v1_funct_2(C_193, A_196, B_194) | ~v1_funct_1(C_193))), inference(cnfTransformation, [status(thm)], [f_74])).
% 11.11/4.17  tff(c_400, plain, (![D_197, C_183, C_193, B_194]: (k1_funct_1(D_197, '#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), C_183, '#skF_6'))=k1_funct_1(C_193, '#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), C_183, '#skF_6')) | ~r2_funct_2(u1_struct_0('#skF_4'), B_194, C_193, D_197) | ~m1_subset_1(D_197, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), B_194))) | ~v1_funct_2(D_197, u1_struct_0('#skF_4'), B_194) | ~v1_funct_1(D_197) | ~m1_subset_1(C_193, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), B_194))) | ~v1_funct_2(C_193, u1_struct_0('#skF_4'), B_194) | ~v1_funct_1(C_193) | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), C_183, '#skF_6') | ~m1_subset_1(C_183, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2(C_183, u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(C_183))), inference(resolution, [status(thm)], [c_320, c_383])).
% 11.11/4.17  tff(c_1474, plain, (![C_183]: (k1_funct_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_4'), '#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), C_183, '#skF_6'))=k1_funct_1('#skF_6', '#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), C_183, '#skF_6')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~m1_subset_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_4')) | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), C_183, '#skF_6') | ~m1_subset_1(C_183, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2(C_183, u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(C_183))), inference(resolution, [status(thm)], [c_1472, c_400])).
% 11.11/4.17  tff(c_1477, plain, (![C_183]: (k1_funct_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_4'), '#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), C_183, '#skF_6'))=k1_funct_1('#skF_6', '#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), C_183, '#skF_6')) | ~m1_subset_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), C_183, '#skF_6') | ~m1_subset_1(C_183, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2(C_183, u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(C_183))), inference(demodulation, [status(thm), theory('equality')], [c_1411, c_1421, c_46, c_44, c_42, c_1474])).
% 11.11/4.17  tff(c_2270, plain, (~m1_subset_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(splitLeft, [status(thm)], [c_1477])).
% 11.11/4.17  tff(c_2295, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_30, c_2270])).
% 11.11/4.17  tff(c_2299, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_260, c_246, c_46, c_44, c_42, c_2295])).
% 11.11/4.17  tff(c_2301, plain, (m1_subset_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(splitRight, [status(thm)], [c_1477])).
% 11.11/4.17  tff(c_16, plain, (![A_14, B_15, C_16, D_22]: (m1_subset_1('#skF_1'(A_14, B_15, C_16, D_22), A_14) | r2_funct_2(A_14, B_15, C_16, D_22) | ~m1_subset_1(D_22, k1_zfmisc_1(k2_zfmisc_1(A_14, B_15))) | ~v1_funct_2(D_22, A_14, B_15) | ~v1_funct_1(D_22) | ~m1_subset_1(C_16, k1_zfmisc_1(k2_zfmisc_1(A_14, B_15))) | ~v1_funct_2(C_16, A_14, B_15) | ~v1_funct_1(C_16))), inference(cnfTransformation, [status(thm)], [f_74])).
% 11.11/4.17  tff(c_2328, plain, (![C_16]: (m1_subset_1('#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), C_16, k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_4')), u1_struct_0('#skF_4')) | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), C_16, k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_4')) | ~v1_funct_2(k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_4')) | ~m1_subset_1(C_16, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2(C_16, u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(C_16))), inference(resolution, [status(thm)], [c_2301, c_16])).
% 11.11/4.17  tff(c_2635, plain, (![C_617]: (m1_subset_1('#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), C_617, k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_4')), u1_struct_0('#skF_4')) | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), C_617, k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_4')) | ~m1_subset_1(C_617, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2(C_617, u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(C_617))), inference(demodulation, [status(thm), theory('equality')], [c_1411, c_1421, c_2328])).
% 11.11/4.17  tff(c_8, plain, (![A_9, B_10]: (v1_relat_1(k2_zfmisc_1(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 11.11/4.17  tff(c_6, plain, (![B_8, A_6]: (v1_relat_1(B_8) | ~m1_subset_1(B_8, k1_zfmisc_1(A_6)) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_44])).
% 11.11/4.17  tff(c_88, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_48, c_6])).
% 11.11/4.17  tff(c_91, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_88])).
% 11.11/4.17  tff(c_68, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_209])).
% 11.11/4.17  tff(c_60, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_209])).
% 11.11/4.17  tff(c_66, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_209])).
% 11.11/4.17  tff(c_134, plain, (![A_145, B_146, C_147, D_148]: (k2_partfun1(A_145, B_146, C_147, D_148)=k7_relat_1(C_147, D_148) | ~m1_subset_1(C_147, k1_zfmisc_1(k2_zfmisc_1(A_145, B_146))) | ~v1_funct_1(C_147))), inference(cnfTransformation, [status(thm)], [f_80])).
% 11.11/4.17  tff(c_136, plain, (![D_148]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_5', D_148)=k7_relat_1('#skF_5', D_148) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_48, c_134])).
% 11.11/4.17  tff(c_141, plain, (![D_148]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_5', D_148)=k7_relat_1('#skF_5', D_148))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_136])).
% 11.11/4.17  tff(c_493, plain, (![A_231, B_232, C_233, D_234]: (k2_partfun1(u1_struct_0(A_231), u1_struct_0(B_232), C_233, u1_struct_0(D_234))=k2_tmap_1(A_231, B_232, C_233, D_234) | ~m1_pre_topc(D_234, A_231) | ~m1_subset_1(C_233, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_231), u1_struct_0(B_232)))) | ~v1_funct_2(C_233, u1_struct_0(A_231), u1_struct_0(B_232)) | ~v1_funct_1(C_233) | ~l1_pre_topc(B_232) | ~v2_pre_topc(B_232) | v2_struct_0(B_232) | ~l1_pre_topc(A_231) | ~v2_pre_topc(A_231) | v2_struct_0(A_231))), inference(cnfTransformation, [status(thm)], [f_139])).
% 11.11/4.17  tff(c_497, plain, (![D_234]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_234))=k2_tmap_1('#skF_3', '#skF_2', '#skF_5', D_234) | ~m1_pre_topc(D_234, '#skF_3') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_48, c_493])).
% 11.11/4.17  tff(c_503, plain, (![D_234]: (k7_relat_1('#skF_5', u1_struct_0(D_234))=k2_tmap_1('#skF_3', '#skF_2', '#skF_5', D_234) | ~m1_pre_topc(D_234, '#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_66, c_64, c_52, c_50, c_141, c_497])).
% 11.11/4.17  tff(c_509, plain, (![D_235]: (k7_relat_1('#skF_5', u1_struct_0(D_235))=k2_tmap_1('#skF_3', '#skF_2', '#skF_5', D_235) | ~m1_pre_topc(D_235, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_62, c_68, c_503])).
% 11.11/4.17  tff(c_10, plain, (![C_13, B_12, A_11]: (k1_funct_1(k7_relat_1(C_13, B_12), A_11)=k1_funct_1(C_13, A_11) | ~r2_hidden(A_11, B_12) | ~v1_funct_1(C_13) | ~v1_relat_1(C_13))), inference(cnfTransformation, [status(thm)], [f_54])).
% 11.11/4.17  tff(c_515, plain, (![D_235, A_11]: (k1_funct_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_5', D_235), A_11)=k1_funct_1('#skF_5', A_11) | ~r2_hidden(A_11, u1_struct_0(D_235)) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | ~m1_pre_topc(D_235, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_509, c_10])).
% 11.11/4.17  tff(c_524, plain, (![D_236, A_237]: (k1_funct_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_5', D_236), A_237)=k1_funct_1('#skF_5', A_237) | ~r2_hidden(A_237, u1_struct_0(D_236)) | ~m1_pre_topc(D_236, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_91, c_52, c_515])).
% 11.11/4.17  tff(c_529, plain, (![D_236, A_1]: (k1_funct_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_5', D_236), A_1)=k1_funct_1('#skF_5', A_1) | ~m1_pre_topc(D_236, '#skF_3') | v1_xboole_0(u1_struct_0(D_236)) | ~m1_subset_1(A_1, u1_struct_0(D_236)))), inference(resolution, [status(thm)], [c_2, c_524])).
% 11.11/4.17  tff(c_2638, plain, (![C_617]: (k1_funct_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4'), '#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), C_617, k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_4')))=k1_funct_1('#skF_5', '#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), C_617, k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_4'))) | ~m1_pre_topc('#skF_4', '#skF_3') | v1_xboole_0(u1_struct_0('#skF_4')) | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), C_617, k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_4')) | ~m1_subset_1(C_617, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2(C_617, u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(C_617))), inference(resolution, [status(thm)], [c_2635, c_529])).
% 11.11/4.17  tff(c_2648, plain, (![C_617]: (k1_funct_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4'), '#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), C_617, k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_4')))=k1_funct_1('#skF_5', '#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), C_617, k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_4'))) | v1_xboole_0(u1_struct_0('#skF_4')) | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), C_617, k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_4')) | ~m1_subset_1(C_617, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2(C_617, u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(C_617))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_2638])).
% 11.11/4.17  tff(c_2824, plain, (![C_633]: (k1_funct_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4'), '#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), C_633, k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_4')))=k1_funct_1('#skF_5', '#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), C_633, k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_4'))) | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), C_633, k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_4')) | ~m1_subset_1(C_633, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2(C_633, u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(C_633))), inference(negUnitSimplification, [status(thm)], [c_200, c_2648])).
% 11.11/4.17  tff(c_14, plain, (![D_22, A_14, B_15, C_16]: (k1_funct_1(D_22, '#skF_1'(A_14, B_15, C_16, D_22))!=k1_funct_1(C_16, '#skF_1'(A_14, B_15, C_16, D_22)) | r2_funct_2(A_14, B_15, C_16, D_22) | ~m1_subset_1(D_22, k1_zfmisc_1(k2_zfmisc_1(A_14, B_15))) | ~v1_funct_2(D_22, A_14, B_15) | ~v1_funct_1(D_22) | ~m1_subset_1(C_16, k1_zfmisc_1(k2_zfmisc_1(A_14, B_15))) | ~v1_funct_2(C_16, A_14, B_15) | ~v1_funct_1(C_16))), inference(cnfTransformation, [status(thm)], [f_74])).
% 11.11/4.17  tff(c_2833, plain, (k1_funct_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_4'), '#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4'), k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_4')))!=k1_funct_1('#skF_5', '#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4'), k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_4'))) | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4'), k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_4')) | ~m1_subset_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_4')) | ~m1_subset_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k2_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4')) | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4'), k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_4')) | ~m1_subset_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k2_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_2824, c_14])).
% 11.11/4.17  tff(c_2841, plain, (k1_funct_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_4'), '#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4'), k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_4')))!=k1_funct_1('#skF_5', '#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4'), k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_4'))) | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4'), k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_4')) | ~m1_subset_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_947, c_973, c_947, c_973, c_1411, c_1421, c_2301, c_2833])).
% 11.11/4.17  tff(c_4706, plain, (~m1_subset_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(splitLeft, [status(thm)], [c_2841])).
% 11.11/4.17  tff(c_4709, plain, (~l1_struct_0('#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_30, c_4706])).
% 11.11/4.17  tff(c_4713, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_225, c_246, c_52, c_50, c_48, c_260, c_4709])).
% 11.11/4.17  tff(c_4715, plain, (m1_subset_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(splitRight, [status(thm)], [c_2841])).
% 11.11/4.17  tff(c_972, plain, (k1_funct_1('#skF_5', '#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4'), '#skF_6'))=k1_funct_1('#skF_6', '#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4'), '#skF_6'))), inference(splitRight, [status(thm)], [c_946])).
% 11.11/4.17  tff(c_531, plain, (![D_242, A_243]: (k1_funct_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_5', D_242), A_243)=k1_funct_1('#skF_5', A_243) | ~m1_pre_topc(D_242, '#skF_3') | v1_xboole_0(u1_struct_0(D_242)) | ~m1_subset_1(A_243, u1_struct_0(D_242)))), inference(resolution, [status(thm)], [c_2, c_524])).
% 11.11/4.17  tff(c_537, plain, (![C_183]: (k1_funct_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4'), '#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), C_183, '#skF_6'))=k1_funct_1('#skF_5', '#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), C_183, '#skF_6')) | ~m1_pre_topc('#skF_4', '#skF_3') | v1_xboole_0(u1_struct_0('#skF_4')) | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), C_183, '#skF_6') | ~m1_subset_1(C_183, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2(C_183, u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(C_183))), inference(resolution, [status(thm)], [c_320, c_531])).
% 11.11/4.17  tff(c_546, plain, (![C_183]: (k1_funct_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4'), '#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), C_183, '#skF_6'))=k1_funct_1('#skF_5', '#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), C_183, '#skF_6')) | v1_xboole_0(u1_struct_0('#skF_4')) | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), C_183, '#skF_6') | ~m1_subset_1(C_183, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2(C_183, u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(C_183))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_537])).
% 11.11/4.17  tff(c_547, plain, (![C_183]: (k1_funct_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4'), '#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), C_183, '#skF_6'))=k1_funct_1('#skF_5', '#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), C_183, '#skF_6')) | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), C_183, '#skF_6') | ~m1_subset_1(C_183, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2(C_183, u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(C_183))), inference(negUnitSimplification, [status(thm)], [c_200, c_546])).
% 11.11/4.17  tff(c_4754, plain, (k1_funct_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4'), '#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4'), '#skF_6'))=k1_funct_1('#skF_5', '#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4'), '#skF_6')) | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4'), '#skF_6') | ~v1_funct_2(k2_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4'))), inference(resolution, [status(thm)], [c_4715, c_547])).
% 11.11/4.17  tff(c_4812, plain, (k1_funct_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4'), '#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4'), '#skF_6'))=k1_funct_1('#skF_6', '#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4'), '#skF_6')) | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_947, c_973, c_972, c_4754])).
% 11.11/4.17  tff(c_4813, plain, (k1_funct_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4'), '#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4'), '#skF_6'))=k1_funct_1('#skF_6', '#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4'), '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_38, c_4812])).
% 11.11/4.17  tff(c_4860, plain, (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4'), '#skF_6') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~m1_subset_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k2_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_4813, c_14])).
% 11.11/4.17  tff(c_4865, plain, (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_947, c_973, c_4715, c_46, c_44, c_42, c_4860])).
% 11.11/4.17  tff(c_4867, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_4865])).
% 11.11/4.17  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.11/4.17  
% 11.11/4.17  Inference rules
% 11.11/4.17  ----------------------
% 11.11/4.17  #Ref     : 7
% 11.11/4.17  #Sup     : 1051
% 11.11/4.17  #Fact    : 0
% 11.11/4.17  #Define  : 0
% 11.11/4.17  #Split   : 22
% 11.11/4.17  #Chain   : 0
% 11.11/4.17  #Close   : 0
% 11.11/4.17  
% 11.11/4.17  Ordering : KBO
% 11.11/4.17  
% 11.11/4.17  Simplification rules
% 11.11/4.17  ----------------------
% 11.11/4.17  #Subsume      : 194
% 11.11/4.17  #Demod        : 1279
% 11.11/4.17  #Tautology    : 157
% 11.11/4.17  #SimpNegUnit  : 119
% 11.11/4.17  #BackRed      : 0
% 11.11/4.17  
% 11.11/4.17  #Partial instantiations: 0
% 11.11/4.17  #Strategies tried      : 1
% 11.11/4.17  
% 11.11/4.17  Timing (in seconds)
% 11.11/4.17  ----------------------
% 11.11/4.18  Preprocessing        : 0.59
% 11.11/4.18  Parsing              : 0.31
% 11.11/4.18  CNF conversion       : 0.05
% 11.11/4.18  Main loop            : 2.67
% 11.11/4.18  Inferencing          : 0.86
% 11.11/4.18  Reduction            : 0.85
% 11.11/4.18  Demodulation         : 0.64
% 11.11/4.18  BG Simplification    : 0.10
% 11.11/4.18  Subsumption          : 0.75
% 11.11/4.18  Abstraction          : 0.13
% 11.11/4.18  MUC search           : 0.00
% 11.11/4.18  Cooper               : 0.00
% 11.11/4.18  Total                : 3.32
% 11.11/4.18  Index Insertion      : 0.00
% 11.11/4.18  Index Deletion       : 0.00
% 11.11/4.18  Index Matching       : 0.00
% 11.11/4.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
