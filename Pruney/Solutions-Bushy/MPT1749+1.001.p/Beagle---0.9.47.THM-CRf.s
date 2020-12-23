%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1749+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:20 EST 2020

% Result     : Theorem 5.48s
% Output     : CNFRefutation 5.48s
% Verified   : 
% Statistics : Number of formulae       :  143 ( 894 expanded)
%              Number of leaves         :   37 ( 331 expanded)
%              Depth                    :   21
%              Number of atoms          :  453 (7586 expanded)
%              Number of equality atoms :   47 ( 580 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_funct_2 > v1_funct_2 > r2_hidden > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_funct_2 > k2_tmap_1 > k2_partfun1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_222,negated_conjecture,(
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

tff(f_112,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_funct_2(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_funct_2)).

tff(f_81,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_77,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tmap_1)).

tff(f_88,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_164,axiom,(
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

tff(f_96,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_171,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_177,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

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

tff(c_44,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_222])).

tff(c_42,plain,(
    v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_222])).

tff(c_40,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_222])).

tff(c_101,plain,(
    ! [A_181,B_182,D_183] :
      ( r2_funct_2(A_181,B_182,D_183,D_183)
      | ~ m1_subset_1(D_183,k1_zfmisc_1(k2_zfmisc_1(A_181,B_182)))
      | ~ v1_funct_2(D_183,A_181,B_182)
      | ~ v1_funct_1(D_183) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_103,plain,
    ( r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_6','#skF_6')
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_40,c_101])).

tff(c_108,plain,(
    r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_103])).

tff(c_52,plain,(
    m1_pre_topc('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_222])).

tff(c_60,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_222])).

tff(c_56,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_222])).

tff(c_14,plain,(
    ! [A_24] :
      ( l1_struct_0(A_24)
      | ~ l1_pre_topc(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_50,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_222])).

tff(c_48,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_222])).

tff(c_46,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_222])).

tff(c_149,plain,(
    ! [A_203,B_204,C_205,D_206] :
      ( v1_funct_1(k2_tmap_1(A_203,B_204,C_205,D_206))
      | ~ l1_struct_0(D_206)
      | ~ m1_subset_1(C_205,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_203),u1_struct_0(B_204))))
      | ~ v1_funct_2(C_205,u1_struct_0(A_203),u1_struct_0(B_204))
      | ~ v1_funct_1(C_205)
      | ~ l1_struct_0(B_204)
      | ~ l1_struct_0(A_203) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_156,plain,(
    ! [D_206] :
      ( v1_funct_1(k2_tmap_1('#skF_3','#skF_2','#skF_5',D_206))
      | ~ l1_struct_0(D_206)
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_46,c_149])).

tff(c_163,plain,(
    ! [D_206] :
      ( v1_funct_1(k2_tmap_1('#skF_3','#skF_2','#skF_5',D_206))
      | ~ l1_struct_0(D_206)
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_156])).

tff(c_174,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_163])).

tff(c_177,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_14,c_174])).

tff(c_181,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_177])).

tff(c_183,plain,(
    l1_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_163])).

tff(c_66,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_222])).

tff(c_62,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_222])).

tff(c_69,plain,(
    ! [B_165,A_166] :
      ( l1_pre_topc(B_165)
      | ~ m1_pre_topc(B_165,A_166)
      | ~ l1_pre_topc(A_166) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_72,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_69])).

tff(c_75,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_72])).

tff(c_154,plain,(
    ! [D_206] :
      ( v1_funct_1(k2_tmap_1('#skF_4','#skF_2','#skF_6',D_206))
      | ~ l1_struct_0(D_206)
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_6')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_40,c_149])).

tff(c_160,plain,(
    ! [D_206] :
      ( v1_funct_1(k2_tmap_1('#skF_4','#skF_2','#skF_6',D_206))
      | ~ l1_struct_0(D_206)
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_154])).

tff(c_164,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_160])).

tff(c_167,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_14,c_164])).

tff(c_171,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_167])).

tff(c_172,plain,(
    ! [D_206] :
      ( ~ l1_struct_0('#skF_2')
      | v1_funct_1(k2_tmap_1('#skF_4','#skF_2','#skF_6',D_206))
      | ~ l1_struct_0(D_206) ) ),
    inference(splitRight,[status(thm)],[c_160])).

tff(c_184,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_172])).

tff(c_187,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_14,c_184])).

tff(c_191,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_187])).

tff(c_193,plain,(
    l1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_172])).

tff(c_442,plain,(
    ! [A_258,D_259,C_257,B_260,E_261] :
      ( m1_subset_1('#skF_1'(C_257,A_258,D_259,B_260,E_261),A_258)
      | k2_partfun1(A_258,B_260,C_257,D_259) = E_261
      | ~ m1_subset_1(E_261,k1_zfmisc_1(k2_zfmisc_1(D_259,B_260)))
      | ~ v1_funct_2(E_261,D_259,B_260)
      | ~ v1_funct_1(E_261)
      | ~ m1_subset_1(D_259,k1_zfmisc_1(A_258))
      | v1_xboole_0(D_259)
      | ~ m1_subset_1(C_257,k1_zfmisc_1(k2_zfmisc_1(A_258,B_260)))
      | ~ v1_funct_2(C_257,A_258,B_260)
      | ~ v1_funct_1(C_257)
      | v1_xboole_0(B_260)
      | v1_xboole_0(A_258) ) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_450,plain,(
    ! [C_257,A_258] :
      ( m1_subset_1('#skF_1'(C_257,A_258,u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_6'),A_258)
      | k2_partfun1(A_258,u1_struct_0('#skF_2'),C_257,u1_struct_0('#skF_4')) = '#skF_6'
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(A_258))
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | ~ m1_subset_1(C_257,k1_zfmisc_1(k2_zfmisc_1(A_258,u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_257,A_258,u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_257)
      | v1_xboole_0(u1_struct_0('#skF_2'))
      | v1_xboole_0(A_258) ) ),
    inference(resolution,[status(thm)],[c_40,c_442])).

tff(c_458,plain,(
    ! [C_257,A_258] :
      ( m1_subset_1('#skF_1'(C_257,A_258,u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_6'),A_258)
      | k2_partfun1(A_258,u1_struct_0('#skF_2'),C_257,u1_struct_0('#skF_4')) = '#skF_6'
      | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(A_258))
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | ~ m1_subset_1(C_257,k1_zfmisc_1(k2_zfmisc_1(A_258,u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_257,A_258,u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_257)
      | v1_xboole_0(u1_struct_0('#skF_2'))
      | v1_xboole_0(A_258) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_450])).

tff(c_478,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_458])).

tff(c_18,plain,(
    ! [A_28] :
      ( ~ v1_xboole_0(u1_struct_0(A_28))
      | ~ l1_struct_0(A_28)
      | v2_struct_0(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_481,plain,
    ( ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_478,c_18])).

tff(c_484,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_193,c_481])).

tff(c_486,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_484])).

tff(c_488,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_458])).

tff(c_452,plain,(
    ! [C_257,A_258] :
      ( m1_subset_1('#skF_1'(C_257,A_258,u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_5'),A_258)
      | k2_partfun1(A_258,u1_struct_0('#skF_2'),C_257,u1_struct_0('#skF_3')) = '#skF_5'
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(u1_struct_0('#skF_3'),k1_zfmisc_1(A_258))
      | v1_xboole_0(u1_struct_0('#skF_3'))
      | ~ m1_subset_1(C_257,k1_zfmisc_1(k2_zfmisc_1(A_258,u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_257,A_258,u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_257)
      | v1_xboole_0(u1_struct_0('#skF_2'))
      | v1_xboole_0(A_258) ) ),
    inference(resolution,[status(thm)],[c_46,c_442])).

tff(c_461,plain,(
    ! [C_257,A_258] :
      ( m1_subset_1('#skF_1'(C_257,A_258,u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_5'),A_258)
      | k2_partfun1(A_258,u1_struct_0('#skF_2'),C_257,u1_struct_0('#skF_3')) = '#skF_5'
      | ~ m1_subset_1(u1_struct_0('#skF_3'),k1_zfmisc_1(A_258))
      | v1_xboole_0(u1_struct_0('#skF_3'))
      | ~ m1_subset_1(C_257,k1_zfmisc_1(k2_zfmisc_1(A_258,u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_257,A_258,u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_257)
      | v1_xboole_0(u1_struct_0('#skF_2'))
      | v1_xboole_0(A_258) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_452])).

tff(c_594,plain,(
    ! [C_257,A_258] :
      ( m1_subset_1('#skF_1'(C_257,A_258,u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_5'),A_258)
      | k2_partfun1(A_258,u1_struct_0('#skF_2'),C_257,u1_struct_0('#skF_3')) = '#skF_5'
      | ~ m1_subset_1(u1_struct_0('#skF_3'),k1_zfmisc_1(A_258))
      | v1_xboole_0(u1_struct_0('#skF_3'))
      | ~ m1_subset_1(C_257,k1_zfmisc_1(k2_zfmisc_1(A_258,u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_257,A_258,u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_257)
      | v1_xboole_0(A_258) ) ),
    inference(negUnitSimplification,[status(thm)],[c_488,c_461])).

tff(c_595,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_594])).

tff(c_598,plain,
    ( ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_595,c_18])).

tff(c_601,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_183,c_598])).

tff(c_603,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_601])).

tff(c_605,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_594])).

tff(c_32,plain,(
    ! [B_101,A_99] :
      ( m1_subset_1(u1_struct_0(B_101),k1_zfmisc_1(u1_struct_0(A_99)))
      | ~ m1_pre_topc(B_101,A_99)
      | ~ l1_pre_topc(A_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_54,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_222])).

tff(c_173,plain,(
    l1_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_160])).

tff(c_487,plain,(
    ! [C_257,A_258] :
      ( v1_xboole_0(u1_struct_0('#skF_4'))
      | m1_subset_1('#skF_1'(C_257,A_258,u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_6'),A_258)
      | k2_partfun1(A_258,u1_struct_0('#skF_2'),C_257,u1_struct_0('#skF_4')) = '#skF_6'
      | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(A_258))
      | ~ m1_subset_1(C_257,k1_zfmisc_1(k2_zfmisc_1(A_258,u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_257,A_258,u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_257)
      | v1_xboole_0(A_258) ) ),
    inference(splitRight,[status(thm)],[c_458])).

tff(c_542,plain,(
    v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_487])).

tff(c_545,plain,
    ( ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_542,c_18])).

tff(c_548,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_545])).

tff(c_550,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_548])).

tff(c_552,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_487])).

tff(c_352,plain,(
    ! [C_244,A_245,B_247,E_248,D_246] :
      ( r2_hidden('#skF_1'(C_244,A_245,D_246,B_247,E_248),D_246)
      | k2_partfun1(A_245,B_247,C_244,D_246) = E_248
      | ~ m1_subset_1(E_248,k1_zfmisc_1(k2_zfmisc_1(D_246,B_247)))
      | ~ v1_funct_2(E_248,D_246,B_247)
      | ~ v1_funct_1(E_248)
      | ~ m1_subset_1(D_246,k1_zfmisc_1(A_245))
      | v1_xboole_0(D_246)
      | ~ m1_subset_1(C_244,k1_zfmisc_1(k2_zfmisc_1(A_245,B_247)))
      | ~ v1_funct_2(C_244,A_245,B_247)
      | ~ v1_funct_1(C_244)
      | v1_xboole_0(B_247)
      | v1_xboole_0(A_245) ) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_360,plain,(
    ! [C_244,A_245] :
      ( r2_hidden('#skF_1'(C_244,A_245,u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_6'),u1_struct_0('#skF_4'))
      | k2_partfun1(A_245,u1_struct_0('#skF_2'),C_244,u1_struct_0('#skF_4')) = '#skF_6'
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(A_245))
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | ~ m1_subset_1(C_244,k1_zfmisc_1(k2_zfmisc_1(A_245,u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_244,A_245,u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_244)
      | v1_xboole_0(u1_struct_0('#skF_2'))
      | v1_xboole_0(A_245) ) ),
    inference(resolution,[status(thm)],[c_40,c_352])).

tff(c_368,plain,(
    ! [C_244,A_245] :
      ( r2_hidden('#skF_1'(C_244,A_245,u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_6'),u1_struct_0('#skF_4'))
      | k2_partfun1(A_245,u1_struct_0('#skF_2'),C_244,u1_struct_0('#skF_4')) = '#skF_6'
      | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(A_245))
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | ~ m1_subset_1(C_244,k1_zfmisc_1(k2_zfmisc_1(A_245,u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_244,A_245,u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_244)
      | v1_xboole_0(u1_struct_0('#skF_2'))
      | v1_xboole_0(A_245) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_360])).

tff(c_653,plain,(
    ! [C_244,A_245] :
      ( r2_hidden('#skF_1'(C_244,A_245,u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_6'),u1_struct_0('#skF_4'))
      | k2_partfun1(A_245,u1_struct_0('#skF_2'),C_244,u1_struct_0('#skF_4')) = '#skF_6'
      | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(A_245))
      | ~ m1_subset_1(C_244,k1_zfmisc_1(k2_zfmisc_1(A_245,u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_244,A_245,u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_244)
      | v1_xboole_0(A_245) ) ),
    inference(negUnitSimplification,[status(thm)],[c_488,c_552,c_368])).

tff(c_38,plain,(
    ! [F_162] :
      ( k3_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_5',F_162) = k1_funct_1('#skF_6',F_162)
      | ~ r2_hidden(F_162,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(F_162,u1_struct_0('#skF_3')) ) ),
    inference(cnfTransformation,[status(thm)],[f_222])).

tff(c_503,plain,(
    ! [E_285,A_282,C_281,D_283,B_284] :
      ( k3_funct_2(A_282,B_284,C_281,'#skF_1'(C_281,A_282,D_283,B_284,E_285)) != k1_funct_1(E_285,'#skF_1'(C_281,A_282,D_283,B_284,E_285))
      | k2_partfun1(A_282,B_284,C_281,D_283) = E_285
      | ~ m1_subset_1(E_285,k1_zfmisc_1(k2_zfmisc_1(D_283,B_284)))
      | ~ v1_funct_2(E_285,D_283,B_284)
      | ~ v1_funct_1(E_285)
      | ~ m1_subset_1(D_283,k1_zfmisc_1(A_282))
      | v1_xboole_0(D_283)
      | ~ m1_subset_1(C_281,k1_zfmisc_1(k2_zfmisc_1(A_282,B_284)))
      | ~ v1_funct_2(C_281,A_282,B_284)
      | ~ v1_funct_1(C_281)
      | v1_xboole_0(B_284)
      | v1_xboole_0(A_282) ) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_506,plain,(
    ! [E_285,D_283] :
      ( k1_funct_1(E_285,'#skF_1'('#skF_5',u1_struct_0('#skF_3'),D_283,u1_struct_0('#skF_2'),E_285)) != k1_funct_1('#skF_6','#skF_1'('#skF_5',u1_struct_0('#skF_3'),D_283,u1_struct_0('#skF_2'),E_285))
      | k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_5',D_283) = E_285
      | ~ m1_subset_1(E_285,k1_zfmisc_1(k2_zfmisc_1(D_283,u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_285,D_283,u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_285)
      | ~ m1_subset_1(D_283,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v1_xboole_0(D_283)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | v1_xboole_0(u1_struct_0('#skF_2'))
      | v1_xboole_0(u1_struct_0('#skF_3'))
      | ~ r2_hidden('#skF_1'('#skF_5',u1_struct_0('#skF_3'),D_283,u1_struct_0('#skF_2'),E_285),u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_1'('#skF_5',u1_struct_0('#skF_3'),D_283,u1_struct_0('#skF_2'),E_285),u1_struct_0('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_503])).

tff(c_508,plain,(
    ! [E_285,D_283] :
      ( k1_funct_1(E_285,'#skF_1'('#skF_5',u1_struct_0('#skF_3'),D_283,u1_struct_0('#skF_2'),E_285)) != k1_funct_1('#skF_6','#skF_1'('#skF_5',u1_struct_0('#skF_3'),D_283,u1_struct_0('#skF_2'),E_285))
      | k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_5',D_283) = E_285
      | ~ m1_subset_1(E_285,k1_zfmisc_1(k2_zfmisc_1(D_283,u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_285,D_283,u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_285)
      | ~ m1_subset_1(D_283,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v1_xboole_0(D_283)
      | v1_xboole_0(u1_struct_0('#skF_2'))
      | v1_xboole_0(u1_struct_0('#skF_3'))
      | ~ r2_hidden('#skF_1'('#skF_5',u1_struct_0('#skF_3'),D_283,u1_struct_0('#skF_2'),E_285),u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_1'('#skF_5',u1_struct_0('#skF_3'),D_283,u1_struct_0('#skF_2'),E_285),u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_506])).

tff(c_509,plain,(
    ! [E_285,D_283] :
      ( k1_funct_1(E_285,'#skF_1'('#skF_5',u1_struct_0('#skF_3'),D_283,u1_struct_0('#skF_2'),E_285)) != k1_funct_1('#skF_6','#skF_1'('#skF_5',u1_struct_0('#skF_3'),D_283,u1_struct_0('#skF_2'),E_285))
      | k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_5',D_283) = E_285
      | ~ m1_subset_1(E_285,k1_zfmisc_1(k2_zfmisc_1(D_283,u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_285,D_283,u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_285)
      | ~ m1_subset_1(D_283,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v1_xboole_0(D_283)
      | v1_xboole_0(u1_struct_0('#skF_3'))
      | ~ r2_hidden('#skF_1'('#skF_5',u1_struct_0('#skF_3'),D_283,u1_struct_0('#skF_2'),E_285),u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_1'('#skF_5',u1_struct_0('#skF_3'),D_283,u1_struct_0('#skF_2'),E_285),u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_488,c_508])).

tff(c_1327,plain,(
    ! [E_285,D_283] :
      ( k1_funct_1(E_285,'#skF_1'('#skF_5',u1_struct_0('#skF_3'),D_283,u1_struct_0('#skF_2'),E_285)) != k1_funct_1('#skF_6','#skF_1'('#skF_5',u1_struct_0('#skF_3'),D_283,u1_struct_0('#skF_2'),E_285))
      | k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_5',D_283) = E_285
      | ~ m1_subset_1(E_285,k1_zfmisc_1(k2_zfmisc_1(D_283,u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_285,D_283,u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_285)
      | ~ m1_subset_1(D_283,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v1_xboole_0(D_283)
      | ~ r2_hidden('#skF_1'('#skF_5',u1_struct_0('#skF_3'),D_283,u1_struct_0('#skF_2'),E_285),u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_1'('#skF_5',u1_struct_0('#skF_3'),D_283,u1_struct_0('#skF_2'),E_285),u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_605,c_509])).

tff(c_1330,plain,(
    ! [D_283] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_5',D_283) = '#skF_6'
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(D_283,u1_struct_0('#skF_2'))))
      | ~ v1_funct_2('#skF_6',D_283,u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(D_283,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v1_xboole_0(D_283)
      | ~ r2_hidden('#skF_1'('#skF_5',u1_struct_0('#skF_3'),D_283,u1_struct_0('#skF_2'),'#skF_6'),u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_1'('#skF_5',u1_struct_0('#skF_3'),D_283,u1_struct_0('#skF_2'),'#skF_6'),u1_struct_0('#skF_3')) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_1327])).

tff(c_1334,plain,(
    ! [D_442] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_5',D_442) = '#skF_6'
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(D_442,u1_struct_0('#skF_2'))))
      | ~ v1_funct_2('#skF_6',D_442,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(D_442,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v1_xboole_0(D_442)
      | ~ r2_hidden('#skF_1'('#skF_5',u1_struct_0('#skF_3'),D_442,u1_struct_0('#skF_2'),'#skF_6'),u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_1'('#skF_5',u1_struct_0('#skF_3'),D_442,u1_struct_0('#skF_2'),'#skF_6'),u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_1330])).

tff(c_1338,plain,
    ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | v1_xboole_0(u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_1'('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_6'),u1_struct_0('#skF_3'))
    | k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_4')) = '#skF_6'
    | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_5')
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_653,c_1334])).

tff(c_1341,plain,
    ( v1_xboole_0(u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_1'('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_6'),u1_struct_0('#skF_3'))
    | k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_4')) = '#skF_6'
    | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_42,c_40,c_1338])).

tff(c_1342,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_6'),u1_struct_0('#skF_3'))
    | k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_4')) = '#skF_6'
    | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_605,c_552,c_1341])).

tff(c_1343,plain,(
    ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_1342])).

tff(c_1346,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_1343])).

tff(c_1350,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_1346])).

tff(c_1352,plain,(
    m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_1342])).

tff(c_654,plain,(
    ! [C_307,A_308] :
      ( r2_hidden('#skF_1'(C_307,A_308,u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_6'),u1_struct_0('#skF_4'))
      | k2_partfun1(A_308,u1_struct_0('#skF_2'),C_307,u1_struct_0('#skF_4')) = '#skF_6'
      | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(A_308))
      | ~ m1_subset_1(C_307,k1_zfmisc_1(k2_zfmisc_1(A_308,u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_307,A_308,u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_307)
      | v1_xboole_0(A_308) ) ),
    inference(negUnitSimplification,[status(thm)],[c_488,c_552,c_368])).

tff(c_85,plain,(
    ! [B_172,A_173] :
      ( m1_subset_1(u1_struct_0(B_172),k1_zfmisc_1(u1_struct_0(A_173)))
      | ~ m1_pre_topc(B_172,A_173)
      | ~ l1_pre_topc(A_173) ) ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_34,plain,(
    ! [A_102,C_104,B_103] :
      ( m1_subset_1(A_102,C_104)
      | ~ m1_subset_1(B_103,k1_zfmisc_1(C_104))
      | ~ r2_hidden(A_102,B_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_88,plain,(
    ! [A_102,A_173,B_172] :
      ( m1_subset_1(A_102,u1_struct_0(A_173))
      | ~ r2_hidden(A_102,u1_struct_0(B_172))
      | ~ m1_pre_topc(B_172,A_173)
      | ~ l1_pre_topc(A_173) ) ),
    inference(resolution,[status(thm)],[c_85,c_34])).

tff(c_657,plain,(
    ! [C_307,A_308,A_173] :
      ( m1_subset_1('#skF_1'(C_307,A_308,u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_6'),u1_struct_0(A_173))
      | ~ m1_pre_topc('#skF_4',A_173)
      | ~ l1_pre_topc(A_173)
      | k2_partfun1(A_308,u1_struct_0('#skF_2'),C_307,u1_struct_0('#skF_4')) = '#skF_6'
      | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(A_308))
      | ~ m1_subset_1(C_307,k1_zfmisc_1(k2_zfmisc_1(A_308,u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_307,A_308,u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_307)
      | v1_xboole_0(A_308) ) ),
    inference(resolution,[status(thm)],[c_654,c_88])).

tff(c_1351,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_6'),u1_struct_0('#skF_3'))
    | k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_4')) = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_1342])).

tff(c_1379,plain,(
    ~ m1_subset_1('#skF_1'('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_6'),u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1351])).

tff(c_1382,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_4')) = '#skF_6'
    | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_5')
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_657,c_1379])).

tff(c_1388,plain,
    ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_4')) = '#skF_6'
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_1352,c_56,c_52,c_1382])).

tff(c_1389,plain,(
    k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_4')) = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_605,c_1388])).

tff(c_58,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_222])).

tff(c_64,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_222])).

tff(c_267,plain,(
    ! [A_233,B_234,C_235,D_236] :
      ( k2_partfun1(u1_struct_0(A_233),u1_struct_0(B_234),C_235,u1_struct_0(D_236)) = k2_tmap_1(A_233,B_234,C_235,D_236)
      | ~ m1_pre_topc(D_236,A_233)
      | ~ m1_subset_1(C_235,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_233),u1_struct_0(B_234))))
      | ~ v1_funct_2(C_235,u1_struct_0(A_233),u1_struct_0(B_234))
      | ~ v1_funct_1(C_235)
      | ~ l1_pre_topc(B_234)
      | ~ v2_pre_topc(B_234)
      | v2_struct_0(B_234)
      | ~ l1_pre_topc(A_233)
      | ~ v2_pre_topc(A_233)
      | v2_struct_0(A_233) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_276,plain,(
    ! [D_236] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_236)) = k2_tmap_1('#skF_3','#skF_2','#skF_5',D_236)
      | ~ m1_pre_topc(D_236,'#skF_3')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_46,c_267])).

tff(c_285,plain,(
    ! [D_236] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_236)) = k2_tmap_1('#skF_3','#skF_2','#skF_5',D_236)
      | ~ m1_pre_topc(D_236,'#skF_3')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_64,c_62,c_50,c_48,c_276])).

tff(c_286,plain,(
    ! [D_236] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_236)) = k2_tmap_1('#skF_3','#skF_2','#skF_5',D_236)
      | ~ m1_pre_topc(D_236,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_66,c_285])).

tff(c_1446,plain,
    ( k2_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4') = '#skF_6'
    | ~ m1_pre_topc('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1389,c_286])).

tff(c_1508,plain,(
    k2_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_1446])).

tff(c_36,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_222])).

tff(c_1571,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1508,c_36])).

tff(c_1574,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_1571])).

tff(c_1575,plain,(
    k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_4')) = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_1351])).

tff(c_1629,plain,
    ( k2_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4') = '#skF_6'
    | ~ m1_pre_topc('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1575,c_286])).

tff(c_1691,plain,(
    k2_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_1629])).

tff(c_1704,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1691,c_36])).

tff(c_1707,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_1704])).

%------------------------------------------------------------------------------
