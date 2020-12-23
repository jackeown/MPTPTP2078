%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1749+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:20 EST 2020

% Result     : Theorem 3.15s
% Output     : CNFRefutation 3.30s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 826 expanded)
%              Number of leaves         :   37 ( 311 expanded)
%              Depth                    :   21
%              Number of atoms          :  393 (6795 expanded)
%              Number of equality atoms :   48 ( 561 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_funct_2 > v1_funct_2 > r2_hidden > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_funct_2 > k2_tmap_1 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

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

tff(f_191,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_tmap_1)).

tff(f_103,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_funct_2(A,B,C,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_funct_2)).

tff(f_55,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_139,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ~ v1_xboole_0(B)
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,A,B)
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
             => ! [D] :
                  ( ( ~ v1_xboole_0(D)
                    & m1_subset_1(D,k1_zfmisc_1(A)) )
                 => ! [E] :
                      ( ( v1_funct_1(E)
                        & v1_funct_2(E,D,B)
                        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(D,B))) )
                     => ( ! [F] :
                            ( m1_subset_1(F,A)
                           => ( r2_hidden(F,D)
                             => k3_funct_2(A,B,C,F) = k1_funct_1(E,F) ) )
                       => k2_partfun1(A,B,C,D) = E ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t173_funct_2)).

tff(f_70,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_146,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_62,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_76,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_51,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tmap_1)).

tff(c_32,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_30,plain,(
    v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_28,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_113,plain,(
    ! [A_173,B_174,C_175,D_176] :
      ( r2_funct_2(A_173,B_174,C_175,C_175)
      | ~ m1_subset_1(D_176,k1_zfmisc_1(k2_zfmisc_1(A_173,B_174)))
      | ~ v1_funct_2(D_176,A_173,B_174)
      | ~ v1_funct_1(D_176)
      | ~ m1_subset_1(C_175,k1_zfmisc_1(k2_zfmisc_1(A_173,B_174)))
      | ~ v1_funct_2(C_175,A_173,B_174)
      | ~ v1_funct_1(C_175) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_115,plain,(
    ! [C_175] :
      ( r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),C_175,C_175)
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(C_175,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_175,u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_175) ) ),
    inference(resolution,[status(thm)],[c_28,c_113])).

tff(c_124,plain,(
    ! [C_177] :
      ( r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),C_177,C_177)
      | ~ m1_subset_1(C_177,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_177,u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_177) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_115])).

tff(c_126,plain,
    ( r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_6','#skF_6')
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_28,c_124])).

tff(c_129,plain,(
    r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_126])).

tff(c_40,plain,(
    m1_pre_topc('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_44,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_4,plain,(
    ! [A_16] :
      ( l1_struct_0(A_16)
      | ~ l1_pre_topc(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_48,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_50,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_54,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_162,plain,(
    ! [B_189,A_188,D_190,C_191,E_192] :
      ( r2_hidden('#skF_1'(A_188,B_189,D_190,C_191,E_192),D_190)
      | k2_partfun1(A_188,B_189,C_191,D_190) = E_192
      | ~ m1_subset_1(E_192,k1_zfmisc_1(k2_zfmisc_1(D_190,B_189)))
      | ~ v1_funct_2(E_192,D_190,B_189)
      | ~ v1_funct_1(E_192)
      | ~ m1_subset_1(D_190,k1_zfmisc_1(A_188))
      | v1_xboole_0(D_190)
      | ~ m1_subset_1(C_191,k1_zfmisc_1(k2_zfmisc_1(A_188,B_189)))
      | ~ v1_funct_2(C_191,A_188,B_189)
      | ~ v1_funct_1(C_191)
      | v1_xboole_0(B_189)
      | v1_xboole_0(A_188) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_164,plain,(
    ! [A_188,C_191] :
      ( r2_hidden('#skF_1'(A_188,u1_struct_0('#skF_2'),u1_struct_0('#skF_4'),C_191,'#skF_6'),u1_struct_0('#skF_4'))
      | k2_partfun1(A_188,u1_struct_0('#skF_2'),C_191,u1_struct_0('#skF_4')) = '#skF_6'
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(A_188))
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | ~ m1_subset_1(C_191,k1_zfmisc_1(k2_zfmisc_1(A_188,u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_191,A_188,u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_191)
      | v1_xboole_0(u1_struct_0('#skF_2'))
      | v1_xboole_0(A_188) ) ),
    inference(resolution,[status(thm)],[c_28,c_162])).

tff(c_169,plain,(
    ! [A_188,C_191] :
      ( r2_hidden('#skF_1'(A_188,u1_struct_0('#skF_2'),u1_struct_0('#skF_4'),C_191,'#skF_6'),u1_struct_0('#skF_4'))
      | k2_partfun1(A_188,u1_struct_0('#skF_2'),C_191,u1_struct_0('#skF_4')) = '#skF_6'
      | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(A_188))
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | ~ m1_subset_1(C_191,k1_zfmisc_1(k2_zfmisc_1(A_188,u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_191,A_188,u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_191)
      | v1_xboole_0(u1_struct_0('#skF_2'))
      | v1_xboole_0(A_188) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_164])).

tff(c_173,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_169])).

tff(c_8,plain,(
    ! [A_20] :
      ( ~ v1_xboole_0(u1_struct_0(A_20))
      | ~ l1_struct_0(A_20)
      | v2_struct_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_176,plain,
    ( ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_173,c_8])).

tff(c_179,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_176])).

tff(c_182,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_4,c_179])).

tff(c_186,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_182])).

tff(c_188,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_169])).

tff(c_38,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_36,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_34,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_166,plain,(
    ! [A_188,C_191] :
      ( r2_hidden('#skF_1'(A_188,u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),C_191,'#skF_5'),u1_struct_0('#skF_3'))
      | k2_partfun1(A_188,u1_struct_0('#skF_2'),C_191,u1_struct_0('#skF_3')) = '#skF_5'
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(u1_struct_0('#skF_3'),k1_zfmisc_1(A_188))
      | v1_xboole_0(u1_struct_0('#skF_3'))
      | ~ m1_subset_1(C_191,k1_zfmisc_1(k2_zfmisc_1(A_188,u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_191,A_188,u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_191)
      | v1_xboole_0(u1_struct_0('#skF_2'))
      | v1_xboole_0(A_188) ) ),
    inference(resolution,[status(thm)],[c_34,c_162])).

tff(c_172,plain,(
    ! [A_188,C_191] :
      ( r2_hidden('#skF_1'(A_188,u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),C_191,'#skF_5'),u1_struct_0('#skF_3'))
      | k2_partfun1(A_188,u1_struct_0('#skF_2'),C_191,u1_struct_0('#skF_3')) = '#skF_5'
      | ~ m1_subset_1(u1_struct_0('#skF_3'),k1_zfmisc_1(A_188))
      | v1_xboole_0(u1_struct_0('#skF_3'))
      | ~ m1_subset_1(C_191,k1_zfmisc_1(k2_zfmisc_1(A_188,u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_191,A_188,u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_191)
      | v1_xboole_0(u1_struct_0('#skF_2'))
      | v1_xboole_0(A_188) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_166])).

tff(c_218,plain,(
    ! [A_188,C_191] :
      ( r2_hidden('#skF_1'(A_188,u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),C_191,'#skF_5'),u1_struct_0('#skF_3'))
      | k2_partfun1(A_188,u1_struct_0('#skF_2'),C_191,u1_struct_0('#skF_3')) = '#skF_5'
      | ~ m1_subset_1(u1_struct_0('#skF_3'),k1_zfmisc_1(A_188))
      | v1_xboole_0(u1_struct_0('#skF_3'))
      | ~ m1_subset_1(C_191,k1_zfmisc_1(k2_zfmisc_1(A_188,u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_191,A_188,u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_191)
      | v1_xboole_0(A_188) ) ),
    inference(negUnitSimplification,[status(thm)],[c_188,c_172])).

tff(c_219,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_218])).

tff(c_222,plain,
    ( ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_219,c_8])).

tff(c_225,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_222])).

tff(c_228,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_4,c_225])).

tff(c_232,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_228])).

tff(c_234,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_218])).

tff(c_22,plain,(
    ! [B_97,A_95] :
      ( m1_subset_1(u1_struct_0(B_97),k1_zfmisc_1(u1_struct_0(A_95)))
      | ~ m1_pre_topc(B_97,A_95)
      | ~ l1_pre_topc(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_57,plain,(
    ! [B_158,A_159] :
      ( l1_pre_topc(B_158)
      | ~ m1_pre_topc(B_158,A_159)
      | ~ l1_pre_topc(A_159) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_60,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_57])).

tff(c_63,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_60])).

tff(c_42,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_187,plain,(
    ! [A_188,C_191] :
      ( v1_xboole_0(u1_struct_0('#skF_4'))
      | r2_hidden('#skF_1'(A_188,u1_struct_0('#skF_2'),u1_struct_0('#skF_4'),C_191,'#skF_6'),u1_struct_0('#skF_4'))
      | k2_partfun1(A_188,u1_struct_0('#skF_2'),C_191,u1_struct_0('#skF_4')) = '#skF_6'
      | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(A_188))
      | ~ m1_subset_1(C_191,k1_zfmisc_1(k2_zfmisc_1(A_188,u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_191,A_188,u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_191)
      | v1_xboole_0(A_188) ) ),
    inference(splitRight,[status(thm)],[c_169])).

tff(c_189,plain,(
    v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_187])).

tff(c_205,plain,
    ( ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_189,c_8])).

tff(c_208,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_205])).

tff(c_211,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_4,c_208])).

tff(c_215,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_211])).

tff(c_217,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_187])).

tff(c_65,plain,(
    ! [A_162,B_163,C_164,D_165] :
      ( k2_partfun1(A_162,B_163,C_164,D_165) = k7_relat_1(C_164,D_165)
      | ~ m1_subset_1(C_164,k1_zfmisc_1(k2_zfmisc_1(A_162,B_163)))
      | ~ v1_funct_1(C_164) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_69,plain,(
    ! [D_165] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_5',D_165) = k7_relat_1('#skF_5',D_165)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_34,c_65])).

tff(c_75,plain,(
    ! [D_165] : k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_5',D_165) = k7_relat_1('#skF_5',D_165) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_69])).

tff(c_216,plain,(
    ! [A_188,C_191] :
      ( r2_hidden('#skF_1'(A_188,u1_struct_0('#skF_2'),u1_struct_0('#skF_4'),C_191,'#skF_6'),u1_struct_0('#skF_4'))
      | k2_partfun1(A_188,u1_struct_0('#skF_2'),C_191,u1_struct_0('#skF_4')) = '#skF_6'
      | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(A_188))
      | ~ m1_subset_1(C_191,k1_zfmisc_1(k2_zfmisc_1(A_188,u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_191,A_188,u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_191)
      | v1_xboole_0(A_188) ) ),
    inference(splitRight,[status(thm)],[c_187])).

tff(c_26,plain,(
    ! [F_155] :
      ( k3_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_5',F_155) = k1_funct_1('#skF_6',F_155)
      | ~ r2_hidden(F_155,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(F_155,u1_struct_0('#skF_3')) ) ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_326,plain,(
    ! [B_212,C_214,A_211,D_213,E_215] :
      ( k3_funct_2(A_211,B_212,C_214,'#skF_1'(A_211,B_212,D_213,C_214,E_215)) != k1_funct_1(E_215,'#skF_1'(A_211,B_212,D_213,C_214,E_215))
      | k2_partfun1(A_211,B_212,C_214,D_213) = E_215
      | ~ m1_subset_1(E_215,k1_zfmisc_1(k2_zfmisc_1(D_213,B_212)))
      | ~ v1_funct_2(E_215,D_213,B_212)
      | ~ v1_funct_1(E_215)
      | ~ m1_subset_1(D_213,k1_zfmisc_1(A_211))
      | v1_xboole_0(D_213)
      | ~ m1_subset_1(C_214,k1_zfmisc_1(k2_zfmisc_1(A_211,B_212)))
      | ~ v1_funct_2(C_214,A_211,B_212)
      | ~ v1_funct_1(C_214)
      | v1_xboole_0(B_212)
      | v1_xboole_0(A_211) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_329,plain,(
    ! [E_215,D_213] :
      ( k1_funct_1(E_215,'#skF_1'(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),D_213,'#skF_5',E_215)) != k1_funct_1('#skF_6','#skF_1'(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),D_213,'#skF_5',E_215))
      | k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_5',D_213) = E_215
      | ~ m1_subset_1(E_215,k1_zfmisc_1(k2_zfmisc_1(D_213,u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_215,D_213,u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_215)
      | ~ m1_subset_1(D_213,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v1_xboole_0(D_213)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | v1_xboole_0(u1_struct_0('#skF_2'))
      | v1_xboole_0(u1_struct_0('#skF_3'))
      | ~ r2_hidden('#skF_1'(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),D_213,'#skF_5',E_215),u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),D_213,'#skF_5',E_215),u1_struct_0('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_326])).

tff(c_331,plain,(
    ! [E_215,D_213] :
      ( k1_funct_1(E_215,'#skF_1'(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),D_213,'#skF_5',E_215)) != k1_funct_1('#skF_6','#skF_1'(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),D_213,'#skF_5',E_215))
      | k7_relat_1('#skF_5',D_213) = E_215
      | ~ m1_subset_1(E_215,k1_zfmisc_1(k2_zfmisc_1(D_213,u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_215,D_213,u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_215)
      | ~ m1_subset_1(D_213,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v1_xboole_0(D_213)
      | v1_xboole_0(u1_struct_0('#skF_2'))
      | v1_xboole_0(u1_struct_0('#skF_3'))
      | ~ r2_hidden('#skF_1'(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),D_213,'#skF_5',E_215),u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),D_213,'#skF_5',E_215),u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_75,c_329])).

tff(c_332,plain,(
    ! [E_215,D_213] :
      ( k1_funct_1(E_215,'#skF_1'(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),D_213,'#skF_5',E_215)) != k1_funct_1('#skF_6','#skF_1'(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),D_213,'#skF_5',E_215))
      | k7_relat_1('#skF_5',D_213) = E_215
      | ~ m1_subset_1(E_215,k1_zfmisc_1(k2_zfmisc_1(D_213,u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_215,D_213,u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_215)
      | ~ m1_subset_1(D_213,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v1_xboole_0(D_213)
      | ~ r2_hidden('#skF_1'(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),D_213,'#skF_5',E_215),u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),D_213,'#skF_5',E_215),u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_234,c_188,c_331])).

tff(c_335,plain,(
    ! [D_213] :
      ( k7_relat_1('#skF_5',D_213) = '#skF_6'
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(D_213,u1_struct_0('#skF_2'))))
      | ~ v1_funct_2('#skF_6',D_213,u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(D_213,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v1_xboole_0(D_213)
      | ~ r2_hidden('#skF_1'(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),D_213,'#skF_5','#skF_6'),u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),D_213,'#skF_5','#skF_6'),u1_struct_0('#skF_3')) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_332])).

tff(c_339,plain,(
    ! [D_218] :
      ( k7_relat_1('#skF_5',D_218) = '#skF_6'
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(D_218,u1_struct_0('#skF_2'))))
      | ~ v1_funct_2('#skF_6',D_218,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(D_218,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v1_xboole_0(D_218)
      | ~ r2_hidden('#skF_1'(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),D_218,'#skF_5','#skF_6'),u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),D_218,'#skF_5','#skF_6'),u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_335])).

tff(c_343,plain,
    ( k7_relat_1('#skF_5',u1_struct_0('#skF_4')) = '#skF_6'
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | v1_xboole_0(u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),u1_struct_0('#skF_4'),'#skF_5','#skF_6'),u1_struct_0('#skF_3'))
    | k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_4')) = '#skF_6'
    | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_5')
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_216,c_339])).

tff(c_346,plain,
    ( v1_xboole_0(u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),u1_struct_0('#skF_4'),'#skF_5','#skF_6'),u1_struct_0('#skF_3'))
    | k7_relat_1('#skF_5',u1_struct_0('#skF_4')) = '#skF_6'
    | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_75,c_30,c_28,c_343])).

tff(c_347,plain,
    ( ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),u1_struct_0('#skF_4'),'#skF_5','#skF_6'),u1_struct_0('#skF_3'))
    | k7_relat_1('#skF_5',u1_struct_0('#skF_4')) = '#skF_6'
    | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_234,c_217,c_346])).

tff(c_348,plain,(
    ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_347])).

tff(c_351,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_348])).

tff(c_355,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_40,c_351])).

tff(c_357,plain,(
    m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_347])).

tff(c_237,plain,(
    ! [A_202,E_206,D_204,B_203,C_205] :
      ( m1_subset_1('#skF_1'(A_202,B_203,D_204,C_205,E_206),A_202)
      | k2_partfun1(A_202,B_203,C_205,D_204) = E_206
      | ~ m1_subset_1(E_206,k1_zfmisc_1(k2_zfmisc_1(D_204,B_203)))
      | ~ v1_funct_2(E_206,D_204,B_203)
      | ~ v1_funct_1(E_206)
      | ~ m1_subset_1(D_204,k1_zfmisc_1(A_202))
      | v1_xboole_0(D_204)
      | ~ m1_subset_1(C_205,k1_zfmisc_1(k2_zfmisc_1(A_202,B_203)))
      | ~ v1_funct_2(C_205,A_202,B_203)
      | ~ v1_funct_1(C_205)
      | v1_xboole_0(B_203)
      | v1_xboole_0(A_202) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_239,plain,(
    ! [A_202,C_205] :
      ( m1_subset_1('#skF_1'(A_202,u1_struct_0('#skF_2'),u1_struct_0('#skF_4'),C_205,'#skF_6'),A_202)
      | k2_partfun1(A_202,u1_struct_0('#skF_2'),C_205,u1_struct_0('#skF_4')) = '#skF_6'
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(A_202))
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | ~ m1_subset_1(C_205,k1_zfmisc_1(k2_zfmisc_1(A_202,u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_205,A_202,u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_205)
      | v1_xboole_0(u1_struct_0('#skF_2'))
      | v1_xboole_0(A_202) ) ),
    inference(resolution,[status(thm)],[c_28,c_237])).

tff(c_244,plain,(
    ! [A_202,C_205] :
      ( m1_subset_1('#skF_1'(A_202,u1_struct_0('#skF_2'),u1_struct_0('#skF_4'),C_205,'#skF_6'),A_202)
      | k2_partfun1(A_202,u1_struct_0('#skF_2'),C_205,u1_struct_0('#skF_4')) = '#skF_6'
      | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(A_202))
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | ~ m1_subset_1(C_205,k1_zfmisc_1(k2_zfmisc_1(A_202,u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_205,A_202,u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_205)
      | v1_xboole_0(u1_struct_0('#skF_2'))
      | v1_xboole_0(A_202) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_239])).

tff(c_245,plain,(
    ! [A_202,C_205] :
      ( m1_subset_1('#skF_1'(A_202,u1_struct_0('#skF_2'),u1_struct_0('#skF_4'),C_205,'#skF_6'),A_202)
      | k2_partfun1(A_202,u1_struct_0('#skF_2'),C_205,u1_struct_0('#skF_4')) = '#skF_6'
      | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(A_202))
      | ~ m1_subset_1(C_205,k1_zfmisc_1(k2_zfmisc_1(A_202,u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_205,A_202,u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_205)
      | v1_xboole_0(A_202) ) ),
    inference(negUnitSimplification,[status(thm)],[c_188,c_217,c_244])).

tff(c_356,plain,
    ( ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),u1_struct_0('#skF_4'),'#skF_5','#skF_6'),u1_struct_0('#skF_3'))
    | k7_relat_1('#skF_5',u1_struct_0('#skF_4')) = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_347])).

tff(c_361,plain,(
    ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),u1_struct_0('#skF_4'),'#skF_5','#skF_6'),u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_356])).

tff(c_385,plain,
    ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_4')) = '#skF_6'
    | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_5')
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_245,c_361])).

tff(c_388,plain,
    ( k7_relat_1('#skF_5',u1_struct_0('#skF_4')) = '#skF_6'
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_357,c_75,c_385])).

tff(c_389,plain,(
    k7_relat_1('#skF_5',u1_struct_0('#skF_4')) = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_234,c_388])).

tff(c_46,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_52,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_139,plain,(
    ! [A_183,B_184,C_185,D_186] :
      ( k2_partfun1(u1_struct_0(A_183),u1_struct_0(B_184),C_185,u1_struct_0(D_186)) = k2_tmap_1(A_183,B_184,C_185,D_186)
      | ~ m1_pre_topc(D_186,A_183)
      | ~ m1_subset_1(C_185,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_183),u1_struct_0(B_184))))
      | ~ v1_funct_2(C_185,u1_struct_0(A_183),u1_struct_0(B_184))
      | ~ v1_funct_1(C_185)
      | ~ l1_pre_topc(B_184)
      | ~ v2_pre_topc(B_184)
      | v2_struct_0(B_184)
      | ~ l1_pre_topc(A_183)
      | ~ v2_pre_topc(A_183)
      | v2_struct_0(A_183) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_143,plain,(
    ! [D_186] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_186)) = k2_tmap_1('#skF_3','#skF_2','#skF_5',D_186)
      | ~ m1_pre_topc(D_186,'#skF_3')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_34,c_139])).

tff(c_150,plain,(
    ! [D_186] :
      ( k7_relat_1('#skF_5',u1_struct_0(D_186)) = k2_tmap_1('#skF_3','#skF_2','#skF_5',D_186)
      | ~ m1_pre_topc(D_186,'#skF_3')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_52,c_50,c_38,c_36,c_75,c_143])).

tff(c_151,plain,(
    ! [D_186] :
      ( k7_relat_1('#skF_5',u1_struct_0(D_186)) = k2_tmap_1('#skF_3','#skF_2','#skF_5',D_186)
      | ~ m1_pre_topc(D_186,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_54,c_150])).

tff(c_393,plain,
    ( k2_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4') = '#skF_6'
    | ~ m1_pre_topc('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_389,c_151])).

tff(c_400,plain,(
    k2_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_393])).

tff(c_24,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_404,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_400,c_24])).

tff(c_407,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_404])).

tff(c_408,plain,(
    k7_relat_1('#skF_5',u1_struct_0('#skF_4')) = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_356])).

tff(c_434,plain,
    ( k2_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4') = '#skF_6'
    | ~ m1_pre_topc('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_408,c_151])).

tff(c_441,plain,(
    k2_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_434])).

tff(c_445,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_441,c_24])).

tff(c_448,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_445])).

%------------------------------------------------------------------------------
