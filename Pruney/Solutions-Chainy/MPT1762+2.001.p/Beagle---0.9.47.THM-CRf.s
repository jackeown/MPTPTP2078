%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:10 EST 2020

% Result     : Theorem 16.04s
% Output     : CNFRefutation 16.17s
% Verified   : 
% Statistics : Number of formulae       :  170 (2740 expanded)
%              Number of leaves         :   46 (1061 expanded)
%              Depth                    :   27
%              Number of atoms          :  525 (23243 expanded)
%              Number of equality atoms :   40 (1423 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_funct_2 > v1_funct_2 > r2_hidden > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k3_funct_2 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k3_tmap_1,type,(
    k3_tmap_1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff('#skF_7',type,(
    '#skF_7': $i )).

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

tff(f_249,negated_conjecture,(
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
                  & m1_pre_topc(C,A) )
               => ! [D] :
                    ( ( ~ v2_struct_0(D)
                      & m1_pre_topc(D,A) )
                   => ! [E] :
                        ( ( v1_funct_1(E)
                          & v1_funct_2(E,u1_struct_0(D),u1_struct_0(B))
                          & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D),u1_struct_0(B)))) )
                       => ( m1_pre_topc(C,D)
                         => ! [F] :
                              ( ( v1_funct_1(F)
                                & v1_funct_2(F,u1_struct_0(C),u1_struct_0(B))
                                & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(B)))) )
                             => ( ! [G] :
                                    ( m1_subset_1(G,u1_struct_0(D))
                                   => ( r2_hidden(G,u1_struct_0(C))
                                     => k3_funct_2(u1_struct_0(D),u1_struct_0(B),E,G) = k1_funct_1(F,G) ) )
                               => r2_funct_2(u1_struct_0(C),u1_struct_0(B),k3_tmap_1(A,B,D,C,E),F) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_tmap_1)).

tff(f_104,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_115,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_196,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_82,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_155,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v2_pre_topc(B)
            & l1_pre_topc(B) )
         => ! [C] :
              ( m1_pre_topc(C,A)
             => ! [D] :
                  ( m1_pre_topc(D,A)
                 => ! [E] :
                      ( ( v1_funct_1(E)
                        & v1_funct_2(E,u1_struct_0(C),u1_struct_0(B))
                        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(B)))) )
                     => ( m1_pre_topc(D,C)
                       => k3_tmap_1(A,B,C,D,E) = k2_partfun1(u1_struct_0(C),u1_struct_0(B),E,u1_struct_0(D)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tmap_1)).

tff(f_185,axiom,(
    ! [A,B,C,D,E] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & ~ v2_struct_0(B)
        & v2_pre_topc(B)
        & l1_pre_topc(B)
        & m1_pre_topc(C,A)
        & m1_pre_topc(D,A)
        & v1_funct_1(E)
        & v1_funct_2(E,u1_struct_0(C),u1_struct_0(B))
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(B)))) )
     => ( v1_funct_1(k3_tmap_1(A,B,C,D,E))
        & v1_funct_2(k3_tmap_1(A,B,C,D,E),u1_struct_0(D),u1_struct_0(B))
        & m1_subset_1(k3_tmap_1(A,B,C,D,E),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D),u1_struct_0(B)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_tmap_1)).

tff(f_76,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_2)).

tff(f_108,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_31,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_192,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_123,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_95,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => k3_funct_2(A,B,C,D) = k1_funct_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(A,B)
       => k1_funct_1(k7_relat_1(C,B),A) = k1_funct_1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_funct_1)).

tff(c_42,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_249])).

tff(c_62,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_249])).

tff(c_76,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_249])).

tff(c_74,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_249])).

tff(c_60,plain,(
    m1_pre_topc('#skF_5','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_249])).

tff(c_122,plain,(
    ! [B_217,A_218] :
      ( v2_pre_topc(B_217)
      | ~ m1_pre_topc(B_217,A_218)
      | ~ l1_pre_topc(A_218)
      | ~ v2_pre_topc(A_218) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_134,plain,
    ( v2_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_122])).

tff(c_144,plain,(
    v2_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_134])).

tff(c_82,plain,(
    ! [B_207,A_208] :
      ( l1_pre_topc(B_207)
      | ~ m1_pre_topc(B_207,A_208)
      | ~ l1_pre_topc(A_208) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_94,plain,
    ( l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_82])).

tff(c_102,plain,(
    l1_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_94])).

tff(c_40,plain,(
    ! [A_82] :
      ( m1_pre_topc(A_82,A_82)
      | ~ l1_pre_topc(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_78,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_249])).

tff(c_52,plain,(
    m1_pre_topc('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_249])).

tff(c_64,plain,(
    m1_pre_topc('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_249])).

tff(c_72,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_249])).

tff(c_70,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_249])).

tff(c_68,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_249])).

tff(c_58,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_249])).

tff(c_56,plain,(
    v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_249])).

tff(c_54,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_249])).

tff(c_189,plain,(
    ! [A_236,B_237,C_238,D_239] :
      ( k2_partfun1(A_236,B_237,C_238,D_239) = k7_relat_1(C_238,D_239)
      | ~ m1_subset_1(C_238,k1_zfmisc_1(k2_zfmisc_1(A_236,B_237)))
      | ~ v1_funct_1(C_238) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_191,plain,(
    ! [D_239] :
      ( k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6',D_239) = k7_relat_1('#skF_6',D_239)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_54,c_189])).

tff(c_196,plain,(
    ! [D_239] : k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6',D_239) = k7_relat_1('#skF_6',D_239) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_191])).

tff(c_584,plain,(
    ! [C_349,A_350,D_348,E_351,B_347] :
      ( k3_tmap_1(A_350,B_347,C_349,D_348,E_351) = k2_partfun1(u1_struct_0(C_349),u1_struct_0(B_347),E_351,u1_struct_0(D_348))
      | ~ m1_pre_topc(D_348,C_349)
      | ~ m1_subset_1(E_351,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_349),u1_struct_0(B_347))))
      | ~ v1_funct_2(E_351,u1_struct_0(C_349),u1_struct_0(B_347))
      | ~ v1_funct_1(E_351)
      | ~ m1_pre_topc(D_348,A_350)
      | ~ m1_pre_topc(C_349,A_350)
      | ~ l1_pre_topc(B_347)
      | ~ v2_pre_topc(B_347)
      | v2_struct_0(B_347)
      | ~ l1_pre_topc(A_350)
      | ~ v2_pre_topc(A_350)
      | v2_struct_0(A_350) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_588,plain,(
    ! [A_350,D_348] :
      ( k3_tmap_1(A_350,'#skF_3','#skF_5',D_348,'#skF_6') = k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6',u1_struct_0(D_348))
      | ~ m1_pre_topc(D_348,'#skF_5')
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_pre_topc(D_348,A_350)
      | ~ m1_pre_topc('#skF_5',A_350)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_350)
      | ~ v2_pre_topc(A_350)
      | v2_struct_0(A_350) ) ),
    inference(resolution,[status(thm)],[c_54,c_584])).

tff(c_594,plain,(
    ! [D_348,A_350] :
      ( k7_relat_1('#skF_6',u1_struct_0(D_348)) = k3_tmap_1(A_350,'#skF_3','#skF_5',D_348,'#skF_6')
      | ~ m1_pre_topc(D_348,'#skF_5')
      | ~ m1_pre_topc(D_348,A_350)
      | ~ m1_pre_topc('#skF_5',A_350)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_350)
      | ~ v2_pre_topc(A_350)
      | v2_struct_0(A_350) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_58,c_56,c_196,c_588])).

tff(c_600,plain,(
    ! [D_352,A_353] :
      ( k7_relat_1('#skF_6',u1_struct_0(D_352)) = k3_tmap_1(A_353,'#skF_3','#skF_5',D_352,'#skF_6')
      | ~ m1_pre_topc(D_352,'#skF_5')
      | ~ m1_pre_topc(D_352,A_353)
      | ~ m1_pre_topc('#skF_5',A_353)
      | ~ l1_pre_topc(A_353)
      | ~ v2_pre_topc(A_353)
      | v2_struct_0(A_353) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_594])).

tff(c_604,plain,
    ( k7_relat_1('#skF_6',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6')
    | ~ m1_pre_topc('#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_600])).

tff(c_612,plain,
    ( k7_relat_1('#skF_6',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_60,c_52,c_604])).

tff(c_613,plain,(
    k7_relat_1('#skF_6',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_612])).

tff(c_606,plain,
    ( k7_relat_1('#skF_6',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_5','#skF_3','#skF_5','#skF_4','#skF_6')
    | ~ m1_pre_topc('#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_5')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_52,c_600])).

tff(c_616,plain,
    ( k7_relat_1('#skF_6',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_5','#skF_3','#skF_5','#skF_4','#skF_6')
    | ~ m1_pre_topc('#skF_5','#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_102,c_52,c_606])).

tff(c_617,plain,
    ( k7_relat_1('#skF_6',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_5','#skF_3','#skF_5','#skF_4','#skF_6')
    | ~ m1_pre_topc('#skF_5','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_616])).

tff(c_631,plain,
    ( k3_tmap_1('#skF_5','#skF_3','#skF_5','#skF_4','#skF_6') = k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6')
    | ~ m1_pre_topc('#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_613,c_617])).

tff(c_632,plain,(
    ~ m1_pre_topc('#skF_5','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_631])).

tff(c_636,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_632])).

tff(c_640,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_636])).

tff(c_642,plain,(
    m1_pre_topc('#skF_5','#skF_5') ),
    inference(splitRight,[status(thm)],[c_631])).

tff(c_641,plain,(
    k3_tmap_1('#skF_5','#skF_3','#skF_5','#skF_4','#skF_6') = k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6') ),
    inference(splitRight,[status(thm)],[c_631])).

tff(c_405,plain,(
    ! [A_274,B_275,D_271,E_273,C_272] :
      ( v1_funct_1(k3_tmap_1(A_274,B_275,C_272,D_271,E_273))
      | ~ m1_subset_1(E_273,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_272),u1_struct_0(B_275))))
      | ~ v1_funct_2(E_273,u1_struct_0(C_272),u1_struct_0(B_275))
      | ~ v1_funct_1(E_273)
      | ~ m1_pre_topc(D_271,A_274)
      | ~ m1_pre_topc(C_272,A_274)
      | ~ l1_pre_topc(B_275)
      | ~ v2_pre_topc(B_275)
      | v2_struct_0(B_275)
      | ~ l1_pre_topc(A_274)
      | ~ v2_pre_topc(A_274)
      | v2_struct_0(A_274) ) ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_407,plain,(
    ! [A_274,D_271] :
      ( v1_funct_1(k3_tmap_1(A_274,'#skF_3','#skF_5',D_271,'#skF_6'))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_pre_topc(D_271,A_274)
      | ~ m1_pre_topc('#skF_5',A_274)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_274)
      | ~ v2_pre_topc(A_274)
      | v2_struct_0(A_274) ) ),
    inference(resolution,[status(thm)],[c_54,c_405])).

tff(c_412,plain,(
    ! [A_274,D_271] :
      ( v1_funct_1(k3_tmap_1(A_274,'#skF_3','#skF_5',D_271,'#skF_6'))
      | ~ m1_pre_topc(D_271,A_274)
      | ~ m1_pre_topc('#skF_5',A_274)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_274)
      | ~ v2_pre_topc(A_274)
      | v2_struct_0(A_274) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_58,c_56,c_407])).

tff(c_413,plain,(
    ! [A_274,D_271] :
      ( v1_funct_1(k3_tmap_1(A_274,'#skF_3','#skF_5',D_271,'#skF_6'))
      | ~ m1_pre_topc(D_271,A_274)
      | ~ m1_pre_topc('#skF_5',A_274)
      | ~ l1_pre_topc(A_274)
      | ~ v2_pre_topc(A_274)
      | v2_struct_0(A_274) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_412])).

tff(c_690,plain,
    ( v1_funct_1(k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6'))
    | ~ m1_pre_topc('#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_5')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_641,c_413])).

tff(c_706,plain,
    ( v1_funct_1(k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_102,c_642,c_52,c_690])).

tff(c_707,plain,(
    v1_funct_1(k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_706])).

tff(c_496,plain,(
    ! [A_312,D_309,C_310,E_311,B_313] :
      ( v1_funct_2(k3_tmap_1(A_312,B_313,C_310,D_309,E_311),u1_struct_0(D_309),u1_struct_0(B_313))
      | ~ m1_subset_1(E_311,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_310),u1_struct_0(B_313))))
      | ~ v1_funct_2(E_311,u1_struct_0(C_310),u1_struct_0(B_313))
      | ~ v1_funct_1(E_311)
      | ~ m1_pre_topc(D_309,A_312)
      | ~ m1_pre_topc(C_310,A_312)
      | ~ l1_pre_topc(B_313)
      | ~ v2_pre_topc(B_313)
      | v2_struct_0(B_313)
      | ~ l1_pre_topc(A_312)
      | ~ v2_pre_topc(A_312)
      | v2_struct_0(A_312) ) ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_498,plain,(
    ! [A_312,D_309] :
      ( v1_funct_2(k3_tmap_1(A_312,'#skF_3','#skF_5',D_309,'#skF_6'),u1_struct_0(D_309),u1_struct_0('#skF_3'))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_pre_topc(D_309,A_312)
      | ~ m1_pre_topc('#skF_5',A_312)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_312)
      | ~ v2_pre_topc(A_312)
      | v2_struct_0(A_312) ) ),
    inference(resolution,[status(thm)],[c_54,c_496])).

tff(c_503,plain,(
    ! [A_312,D_309] :
      ( v1_funct_2(k3_tmap_1(A_312,'#skF_3','#skF_5',D_309,'#skF_6'),u1_struct_0(D_309),u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(D_309,A_312)
      | ~ m1_pre_topc('#skF_5',A_312)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_312)
      | ~ v2_pre_topc(A_312)
      | v2_struct_0(A_312) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_58,c_56,c_498])).

tff(c_504,plain,(
    ! [A_312,D_309] :
      ( v1_funct_2(k3_tmap_1(A_312,'#skF_3','#skF_5',D_309,'#skF_6'),u1_struct_0(D_309),u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(D_309,A_312)
      | ~ m1_pre_topc('#skF_5',A_312)
      | ~ l1_pre_topc(A_312)
      | ~ v2_pre_topc(A_312)
      | v2_struct_0(A_312) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_503])).

tff(c_687,plain,
    ( v1_funct_2(k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
    | ~ m1_pre_topc('#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_5')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_641,c_504])).

tff(c_703,plain,
    ( v1_funct_2(k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_102,c_642,c_52,c_687])).

tff(c_704,plain,(
    v1_funct_2(k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_703])).

tff(c_32,plain,(
    ! [A_74,D_77,B_75,C_76,E_78] :
      ( m1_subset_1(k3_tmap_1(A_74,B_75,C_76,D_77,E_78),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_77),u1_struct_0(B_75))))
      | ~ m1_subset_1(E_78,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_76),u1_struct_0(B_75))))
      | ~ v1_funct_2(E_78,u1_struct_0(C_76),u1_struct_0(B_75))
      | ~ v1_funct_1(E_78)
      | ~ m1_pre_topc(D_77,A_74)
      | ~ m1_pre_topc(C_76,A_74)
      | ~ l1_pre_topc(B_75)
      | ~ v2_pre_topc(B_75)
      | v2_struct_0(B_75)
      | ~ l1_pre_topc(A_74)
      | ~ v2_pre_topc(A_74)
      | v2_struct_0(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_684,plain,
    ( m1_subset_1(k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'))))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1('#skF_6')
    | ~ m1_pre_topc('#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_5')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_641,c_32])).

tff(c_700,plain,
    ( m1_subset_1(k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_102,c_70,c_68,c_642,c_52,c_58,c_56,c_54,c_684])).

tff(c_701,plain,(
    m1_subset_1(k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3')))) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_72,c_700])).

tff(c_50,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_249])).

tff(c_48,plain,(
    v1_funct_2('#skF_7',u1_struct_0('#skF_4'),u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_249])).

tff(c_46,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_249])).

tff(c_278,plain,(
    ! [A_249,B_250,C_251,D_252] :
      ( m1_subset_1('#skF_1'(A_249,B_250,C_251,D_252),A_249)
      | r2_funct_2(A_249,B_250,C_251,D_252)
      | ~ m1_subset_1(D_252,k1_zfmisc_1(k2_zfmisc_1(A_249,B_250)))
      | ~ v1_funct_2(D_252,A_249,B_250)
      | ~ v1_funct_1(D_252)
      | ~ m1_subset_1(C_251,k1_zfmisc_1(k2_zfmisc_1(A_249,B_250)))
      | ~ v1_funct_2(C_251,A_249,B_250)
      | ~ v1_funct_1(C_251) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_282,plain,(
    ! [C_251] :
      ( m1_subset_1('#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),C_251,'#skF_7'),u1_struct_0('#skF_4'))
      | r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),C_251,'#skF_7')
      | ~ v1_funct_2('#skF_7',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1(C_251,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
      | ~ v1_funct_2(C_251,u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1(C_251) ) ),
    inference(resolution,[status(thm)],[c_46,c_278])).

tff(c_288,plain,(
    ! [C_251] :
      ( m1_subset_1('#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),C_251,'#skF_7'),u1_struct_0('#skF_4'))
      | r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),C_251,'#skF_7')
      | ~ m1_subset_1(C_251,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
      | ~ v1_funct_2(C_251,u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1(C_251) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_282])).

tff(c_88,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_82])).

tff(c_98,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_88])).

tff(c_24,plain,(
    ! [A_38] :
      ( l1_struct_0(A_38)
      | ~ l1_pre_topc(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_66,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_249])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r2_hidden(A_1,B_2)
      | v1_xboole_0(B_2)
      | ~ m1_subset_1(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_167,plain,(
    ! [B_225,A_226] :
      ( m1_subset_1(u1_struct_0(B_225),k1_zfmisc_1(u1_struct_0(A_226)))
      | ~ m1_pre_topc(B_225,A_226)
      | ~ l1_pre_topc(A_226) ) ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_4,plain,(
    ! [A_3,C_5,B_4] :
      ( m1_subset_1(A_3,C_5)
      | ~ m1_subset_1(B_4,k1_zfmisc_1(C_5))
      | ~ r2_hidden(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_175,plain,(
    ! [A_230,A_231,B_232] :
      ( m1_subset_1(A_230,u1_struct_0(A_231))
      | ~ r2_hidden(A_230,u1_struct_0(B_232))
      | ~ m1_pre_topc(B_232,A_231)
      | ~ l1_pre_topc(A_231) ) ),
    inference(resolution,[status(thm)],[c_167,c_4])).

tff(c_238,plain,(
    ! [A_246,A_247,B_248] :
      ( m1_subset_1(A_246,u1_struct_0(A_247))
      | ~ m1_pre_topc(B_248,A_247)
      | ~ l1_pre_topc(A_247)
      | v1_xboole_0(u1_struct_0(B_248))
      | ~ m1_subset_1(A_246,u1_struct_0(B_248)) ) ),
    inference(resolution,[status(thm)],[c_2,c_175])).

tff(c_242,plain,(
    ! [A_246] :
      ( m1_subset_1(A_246,u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2')
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | ~ m1_subset_1(A_246,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_64,c_238])).

tff(c_250,plain,(
    ! [A_246] :
      ( m1_subset_1(A_246,u1_struct_0('#skF_2'))
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | ~ m1_subset_1(A_246,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_242])).

tff(c_257,plain,(
    v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_250])).

tff(c_28,plain,(
    ! [A_42] :
      ( ~ v1_xboole_0(u1_struct_0(A_42))
      | ~ l1_struct_0(A_42)
      | v2_struct_0(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_262,plain,
    ( ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_257,c_28])).

tff(c_268,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_262])).

tff(c_271,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_268])).

tff(c_275,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_271])).

tff(c_277,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_250])).

tff(c_434,plain,(
    ! [C_281] :
      ( m1_subset_1('#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),C_281,'#skF_7'),u1_struct_0('#skF_4'))
      | r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),C_281,'#skF_7')
      | ~ m1_subset_1(C_281,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
      | ~ v1_funct_2(C_281,u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1(C_281) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_282])).

tff(c_244,plain,(
    ! [A_246] :
      ( m1_subset_1(A_246,u1_struct_0('#skF_5'))
      | ~ l1_pre_topc('#skF_5')
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | ~ m1_subset_1(A_246,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_52,c_238])).

tff(c_253,plain,(
    ! [A_246] :
      ( m1_subset_1(A_246,u1_struct_0('#skF_5'))
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | ~ m1_subset_1(A_246,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_244])).

tff(c_315,plain,(
    ! [A_246] :
      ( m1_subset_1(A_246,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(A_246,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_277,c_253])).

tff(c_246,plain,(
    ! [A_246] :
      ( m1_subset_1(A_246,u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2')
      | v1_xboole_0(u1_struct_0('#skF_5'))
      | ~ m1_subset_1(A_246,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_60,c_238])).

tff(c_256,plain,(
    ! [A_246] :
      ( m1_subset_1(A_246,u1_struct_0('#skF_2'))
      | v1_xboole_0(u1_struct_0('#skF_5'))
      | ~ m1_subset_1(A_246,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_246])).

tff(c_293,plain,(
    v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_256])).

tff(c_298,plain,
    ( ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_293,c_28])).

tff(c_304,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_298])).

tff(c_307,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_24,c_304])).

tff(c_311,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_307])).

tff(c_313,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_256])).

tff(c_316,plain,(
    ! [A_255] :
      ( m1_subset_1(A_255,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(A_255,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_277,c_253])).

tff(c_20,plain,(
    ! [A_31,B_32,C_33,D_34] :
      ( k3_funct_2(A_31,B_32,C_33,D_34) = k1_funct_1(C_33,D_34)
      | ~ m1_subset_1(D_34,A_31)
      | ~ m1_subset_1(C_33,k1_zfmisc_1(k2_zfmisc_1(A_31,B_32)))
      | ~ v1_funct_2(C_33,A_31,B_32)
      | ~ v1_funct_1(C_33)
      | v1_xboole_0(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_321,plain,(
    ! [B_32,C_33,A_255] :
      ( k3_funct_2(u1_struct_0('#skF_5'),B_32,C_33,A_255) = k1_funct_1(C_33,A_255)
      | ~ m1_subset_1(C_33,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),B_32)))
      | ~ v1_funct_2(C_33,u1_struct_0('#skF_5'),B_32)
      | ~ v1_funct_1(C_33)
      | v1_xboole_0(u1_struct_0('#skF_5'))
      | ~ m1_subset_1(A_255,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_316,c_20])).

tff(c_326,plain,(
    ! [B_256,C_257,A_258] :
      ( k3_funct_2(u1_struct_0('#skF_5'),B_256,C_257,A_258) = k1_funct_1(C_257,A_258)
      | ~ m1_subset_1(C_257,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),B_256)))
      | ~ v1_funct_2(C_257,u1_struct_0('#skF_5'),B_256)
      | ~ v1_funct_1(C_257)
      | ~ m1_subset_1(A_258,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_313,c_321])).

tff(c_328,plain,(
    ! [A_258] :
      ( k3_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6',A_258) = k1_funct_1('#skF_6',A_258)
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(A_258,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_54,c_326])).

tff(c_332,plain,(
    ! [A_259] :
      ( k3_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6',A_259) = k1_funct_1('#skF_6',A_259)
      | ~ m1_subset_1(A_259,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_328])).

tff(c_44,plain,(
    ! [G_203] :
      ( k3_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6',G_203) = k1_funct_1('#skF_7',G_203)
      | ~ r2_hidden(G_203,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(G_203,u1_struct_0('#skF_5')) ) ),
    inference(cnfTransformation,[status(thm)],[f_249])).

tff(c_369,plain,(
    ! [A_265] :
      ( k1_funct_1('#skF_7',A_265) = k1_funct_1('#skF_6',A_265)
      | ~ r2_hidden(A_265,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(A_265,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(A_265,u1_struct_0('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_332,c_44])).

tff(c_373,plain,(
    ! [A_1] :
      ( k1_funct_1('#skF_7',A_1) = k1_funct_1('#skF_6',A_1)
      | ~ m1_subset_1(A_1,u1_struct_0('#skF_5'))
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | ~ m1_subset_1(A_1,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_2,c_369])).

tff(c_377,plain,(
    ! [A_266] :
      ( k1_funct_1('#skF_7',A_266) = k1_funct_1('#skF_6',A_266)
      | ~ m1_subset_1(A_266,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(A_266,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_277,c_373])).

tff(c_381,plain,(
    ! [A_246] :
      ( k1_funct_1('#skF_7',A_246) = k1_funct_1('#skF_6',A_246)
      | ~ m1_subset_1(A_246,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_315,c_377])).

tff(c_442,plain,(
    ! [C_281] :
      ( k1_funct_1('#skF_7','#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),C_281,'#skF_7')) = k1_funct_1('#skF_6','#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),C_281,'#skF_7'))
      | r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),C_281,'#skF_7')
      | ~ m1_subset_1(C_281,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
      | ~ v1_funct_2(C_281,u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1(C_281) ) ),
    inference(resolution,[status(thm)],[c_434,c_381])).

tff(c_911,plain,
    ( k1_funct_1('#skF_7','#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6'),'#skF_7')) = k1_funct_1('#skF_6','#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6'),'#skF_7'))
    | r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6'),'#skF_7')
    | ~ v1_funct_2(k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1(k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6')) ),
    inference(resolution,[status(thm)],[c_701,c_442])).

tff(c_945,plain,
    ( k1_funct_1('#skF_7','#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6'),'#skF_7')) = k1_funct_1('#skF_6','#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6'),'#skF_7'))
    | r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_707,c_704,c_911])).

tff(c_946,plain,(
    k1_funct_1('#skF_7','#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6'),'#skF_7')) = k1_funct_1('#skF_6','#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6'),'#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_945])).

tff(c_10,plain,(
    ! [C_14,A_12,B_13] :
      ( v1_relat_1(C_14)
      | ~ m1_subset_1(C_14,k1_zfmisc_1(k2_zfmisc_1(A_12,B_13))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_114,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_54,c_10])).

tff(c_8,plain,(
    ! [C_11,B_10,A_9] :
      ( k1_funct_1(k7_relat_1(C_11,B_10),A_9) = k1_funct_1(C_11,A_9)
      | ~ r2_hidden(A_9,B_10)
      | ~ v1_funct_1(C_11)
      | ~ v1_relat_1(C_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_461,plain,(
    ! [D_289,A_290,B_291,C_292] :
      ( k1_funct_1(D_289,'#skF_1'(A_290,B_291,C_292,D_289)) != k1_funct_1(C_292,'#skF_1'(A_290,B_291,C_292,D_289))
      | r2_funct_2(A_290,B_291,C_292,D_289)
      | ~ m1_subset_1(D_289,k1_zfmisc_1(k2_zfmisc_1(A_290,B_291)))
      | ~ v1_funct_2(D_289,A_290,B_291)
      | ~ v1_funct_1(D_289)
      | ~ m1_subset_1(C_292,k1_zfmisc_1(k2_zfmisc_1(A_290,B_291)))
      | ~ v1_funct_2(C_292,A_290,B_291)
      | ~ v1_funct_1(C_292) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1274,plain,(
    ! [D_394,B_391,C_392,A_393,B_390] :
      ( k1_funct_1(D_394,'#skF_1'(A_393,B_390,k7_relat_1(C_392,B_391),D_394)) != k1_funct_1(C_392,'#skF_1'(A_393,B_390,k7_relat_1(C_392,B_391),D_394))
      | r2_funct_2(A_393,B_390,k7_relat_1(C_392,B_391),D_394)
      | ~ m1_subset_1(D_394,k1_zfmisc_1(k2_zfmisc_1(A_393,B_390)))
      | ~ v1_funct_2(D_394,A_393,B_390)
      | ~ v1_funct_1(D_394)
      | ~ m1_subset_1(k7_relat_1(C_392,B_391),k1_zfmisc_1(k2_zfmisc_1(A_393,B_390)))
      | ~ v1_funct_2(k7_relat_1(C_392,B_391),A_393,B_390)
      | ~ v1_funct_1(k7_relat_1(C_392,B_391))
      | ~ r2_hidden('#skF_1'(A_393,B_390,k7_relat_1(C_392,B_391),D_394),B_391)
      | ~ v1_funct_1(C_392)
      | ~ v1_relat_1(C_392) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_461])).

tff(c_1284,plain,(
    ! [D_394,A_393,B_390] :
      ( k1_funct_1(D_394,'#skF_1'(A_393,B_390,k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6'),D_394)) != k1_funct_1('#skF_6','#skF_1'(A_393,B_390,k7_relat_1('#skF_6',u1_struct_0('#skF_4')),D_394))
      | r2_funct_2(A_393,B_390,k7_relat_1('#skF_6',u1_struct_0('#skF_4')),D_394)
      | ~ m1_subset_1(D_394,k1_zfmisc_1(k2_zfmisc_1(A_393,B_390)))
      | ~ v1_funct_2(D_394,A_393,B_390)
      | ~ v1_funct_1(D_394)
      | ~ m1_subset_1(k7_relat_1('#skF_6',u1_struct_0('#skF_4')),k1_zfmisc_1(k2_zfmisc_1(A_393,B_390)))
      | ~ v1_funct_2(k7_relat_1('#skF_6',u1_struct_0('#skF_4')),A_393,B_390)
      | ~ v1_funct_1(k7_relat_1('#skF_6',u1_struct_0('#skF_4')))
      | ~ r2_hidden('#skF_1'(A_393,B_390,k7_relat_1('#skF_6',u1_struct_0('#skF_4')),D_394),u1_struct_0('#skF_4'))
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_613,c_1274])).

tff(c_15967,plain,(
    ! [D_1203,A_1204,B_1205] :
      ( k1_funct_1(D_1203,'#skF_1'(A_1204,B_1205,k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6'),D_1203)) != k1_funct_1('#skF_6','#skF_1'(A_1204,B_1205,k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6'),D_1203))
      | r2_funct_2(A_1204,B_1205,k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6'),D_1203)
      | ~ m1_subset_1(D_1203,k1_zfmisc_1(k2_zfmisc_1(A_1204,B_1205)))
      | ~ v1_funct_2(D_1203,A_1204,B_1205)
      | ~ v1_funct_1(D_1203)
      | ~ m1_subset_1(k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(A_1204,B_1205)))
      | ~ v1_funct_2(k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6'),A_1204,B_1205)
      | ~ r2_hidden('#skF_1'(A_1204,B_1205,k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6'),D_1203),u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_58,c_613,c_707,c_613,c_613,c_613,c_613,c_613,c_1284])).

tff(c_16017,plain,
    ( r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6'),'#skF_7')
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
    | ~ v1_funct_2('#skF_7',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1('#skF_7')
    | ~ m1_subset_1(k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
    | ~ v1_funct_2(k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
    | ~ r2_hidden('#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6'),'#skF_7'),u1_struct_0('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_946,c_15967])).

tff(c_16033,plain,
    ( r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6'),'#skF_7')
    | ~ r2_hidden('#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6'),'#skF_7'),u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_704,c_701,c_50,c_48,c_46,c_16017])).

tff(c_16034,plain,(
    ~ r2_hidden('#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6'),'#skF_7'),u1_struct_0('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_16033])).

tff(c_16037,plain,
    ( v1_xboole_0(u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6'),'#skF_7'),u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_2,c_16034])).

tff(c_16040,plain,(
    ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6'),'#skF_7'),u1_struct_0('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_277,c_16037])).

tff(c_16043,plain,
    ( r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6'),'#skF_7')
    | ~ m1_subset_1(k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
    | ~ v1_funct_2(k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1(k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6')) ),
    inference(resolution,[status(thm)],[c_288,c_16040])).

tff(c_16046,plain,(
    r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_707,c_704,c_701,c_16043])).

tff(c_16048,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_16046])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:34:02 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 16.04/7.80  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 16.17/7.82  
% 16.17/7.82  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 16.17/7.82  %$ r2_funct_2 > v1_funct_2 > r2_hidden > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k3_funct_2 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 16.17/7.82  
% 16.17/7.82  %Foreground sorts:
% 16.17/7.82  
% 16.17/7.82  
% 16.17/7.82  %Background operators:
% 16.17/7.82  
% 16.17/7.82  
% 16.17/7.82  %Foreground operators:
% 16.17/7.82  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 16.17/7.82  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 16.17/7.82  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 16.17/7.82  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 16.17/7.82  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 16.17/7.82  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 16.17/7.82  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 16.17/7.82  tff('#skF_7', type, '#skF_7': $i).
% 16.17/7.82  tff('#skF_5', type, '#skF_5': $i).
% 16.17/7.82  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 16.17/7.82  tff('#skF_6', type, '#skF_6': $i).
% 16.17/7.82  tff('#skF_2', type, '#skF_2': $i).
% 16.17/7.82  tff('#skF_3', type, '#skF_3': $i).
% 16.17/7.82  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 16.17/7.82  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 16.17/7.82  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 16.17/7.82  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 16.17/7.82  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 16.17/7.82  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 16.17/7.82  tff('#skF_4', type, '#skF_4': $i).
% 16.17/7.82  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 16.17/7.82  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 16.17/7.82  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 16.17/7.82  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 16.17/7.82  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 16.17/7.82  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 16.17/7.82  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 16.17/7.82  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 16.17/7.82  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 16.17/7.82  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 16.17/7.82  
% 16.17/7.85  tff(f_249, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => (m1_pre_topc(C, D) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => ((![G]: (m1_subset_1(G, u1_struct_0(D)) => (r2_hidden(G, u1_struct_0(C)) => (k3_funct_2(u1_struct_0(D), u1_struct_0(B), E, G) = k1_funct_1(F, G))))) => r2_funct_2(u1_struct_0(C), u1_struct_0(B), k3_tmap_1(A, B, D, C, E), F))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_tmap_1)).
% 16.17/7.85  tff(f_104, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_pre_topc)).
% 16.17/7.85  tff(f_115, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 16.17/7.85  tff(f_196, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tsep_1)).
% 16.17/7.85  tff(f_82, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 16.17/7.85  tff(f_155, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (m1_pre_topc(C, A) => (![D]: (m1_pre_topc(D, A) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (m1_pre_topc(D, C) => (k3_tmap_1(A, B, C, D, E) = k2_partfun1(u1_struct_0(C), u1_struct_0(B), E, u1_struct_0(D)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tmap_1)).
% 16.17/7.85  tff(f_185, axiom, (![A, B, C, D, E]: (((((((((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & ~v2_struct_0(B)) & v2_pre_topc(B)) & l1_pre_topc(B)) & m1_pre_topc(C, A)) & m1_pre_topc(D, A)) & v1_funct_1(E)) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => ((v1_funct_1(k3_tmap_1(A, B, C, D, E)) & v1_funct_2(k3_tmap_1(A, B, C, D, E), u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(k3_tmap_1(A, B, C, D, E), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_tmap_1)).
% 16.17/7.85  tff(f_76, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_funct_2(A, B, C, D) <=> (![E]: (m1_subset_1(E, A) => (k1_funct_1(C, E) = k1_funct_1(D, E))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_funct_2)).
% 16.17/7.85  tff(f_108, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 16.17/7.85  tff(f_31, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 16.17/7.85  tff(f_192, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 16.17/7.85  tff(f_37, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 16.17/7.85  tff(f_123, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 16.17/7.85  tff(f_95, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => (k3_funct_2(A, B, C, D) = k1_funct_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 16.17/7.85  tff(f_56, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 16.17/7.85  tff(f_52, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, B) => (k1_funct_1(k7_relat_1(C, B), A) = k1_funct_1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_funct_1)).
% 16.17/7.85  tff(c_42, plain, (~r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_249])).
% 16.17/7.85  tff(c_62, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_249])).
% 16.17/7.85  tff(c_76, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_249])).
% 16.17/7.85  tff(c_74, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_249])).
% 16.17/7.85  tff(c_60, plain, (m1_pre_topc('#skF_5', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_249])).
% 16.17/7.85  tff(c_122, plain, (![B_217, A_218]: (v2_pre_topc(B_217) | ~m1_pre_topc(B_217, A_218) | ~l1_pre_topc(A_218) | ~v2_pre_topc(A_218))), inference(cnfTransformation, [status(thm)], [f_104])).
% 16.17/7.85  tff(c_134, plain, (v2_pre_topc('#skF_5') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_60, c_122])).
% 16.17/7.85  tff(c_144, plain, (v2_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_134])).
% 16.17/7.85  tff(c_82, plain, (![B_207, A_208]: (l1_pre_topc(B_207) | ~m1_pre_topc(B_207, A_208) | ~l1_pre_topc(A_208))), inference(cnfTransformation, [status(thm)], [f_115])).
% 16.17/7.85  tff(c_94, plain, (l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_60, c_82])).
% 16.17/7.85  tff(c_102, plain, (l1_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_94])).
% 16.17/7.85  tff(c_40, plain, (![A_82]: (m1_pre_topc(A_82, A_82) | ~l1_pre_topc(A_82))), inference(cnfTransformation, [status(thm)], [f_196])).
% 16.17/7.85  tff(c_78, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_249])).
% 16.17/7.85  tff(c_52, plain, (m1_pre_topc('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_249])).
% 16.17/7.85  tff(c_64, plain, (m1_pre_topc('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_249])).
% 16.17/7.85  tff(c_72, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_249])).
% 16.17/7.85  tff(c_70, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_249])).
% 16.17/7.85  tff(c_68, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_249])).
% 16.17/7.85  tff(c_58, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_249])).
% 16.17/7.85  tff(c_56, plain, (v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_249])).
% 16.17/7.85  tff(c_54, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_249])).
% 16.17/7.85  tff(c_189, plain, (![A_236, B_237, C_238, D_239]: (k2_partfun1(A_236, B_237, C_238, D_239)=k7_relat_1(C_238, D_239) | ~m1_subset_1(C_238, k1_zfmisc_1(k2_zfmisc_1(A_236, B_237))) | ~v1_funct_1(C_238))), inference(cnfTransformation, [status(thm)], [f_82])).
% 16.17/7.85  tff(c_191, plain, (![D_239]: (k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', D_239)=k7_relat_1('#skF_6', D_239) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_54, c_189])).
% 16.17/7.85  tff(c_196, plain, (![D_239]: (k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', D_239)=k7_relat_1('#skF_6', D_239))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_191])).
% 16.17/7.85  tff(c_584, plain, (![C_349, A_350, D_348, E_351, B_347]: (k3_tmap_1(A_350, B_347, C_349, D_348, E_351)=k2_partfun1(u1_struct_0(C_349), u1_struct_0(B_347), E_351, u1_struct_0(D_348)) | ~m1_pre_topc(D_348, C_349) | ~m1_subset_1(E_351, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_349), u1_struct_0(B_347)))) | ~v1_funct_2(E_351, u1_struct_0(C_349), u1_struct_0(B_347)) | ~v1_funct_1(E_351) | ~m1_pre_topc(D_348, A_350) | ~m1_pre_topc(C_349, A_350) | ~l1_pre_topc(B_347) | ~v2_pre_topc(B_347) | v2_struct_0(B_347) | ~l1_pre_topc(A_350) | ~v2_pre_topc(A_350) | v2_struct_0(A_350))), inference(cnfTransformation, [status(thm)], [f_155])).
% 16.17/7.85  tff(c_588, plain, (![A_350, D_348]: (k3_tmap_1(A_350, '#skF_3', '#skF_5', D_348, '#skF_6')=k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', u1_struct_0(D_348)) | ~m1_pre_topc(D_348, '#skF_5') | ~v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_6') | ~m1_pre_topc(D_348, A_350) | ~m1_pre_topc('#skF_5', A_350) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc(A_350) | ~v2_pre_topc(A_350) | v2_struct_0(A_350))), inference(resolution, [status(thm)], [c_54, c_584])).
% 16.17/7.85  tff(c_594, plain, (![D_348, A_350]: (k7_relat_1('#skF_6', u1_struct_0(D_348))=k3_tmap_1(A_350, '#skF_3', '#skF_5', D_348, '#skF_6') | ~m1_pre_topc(D_348, '#skF_5') | ~m1_pre_topc(D_348, A_350) | ~m1_pre_topc('#skF_5', A_350) | v2_struct_0('#skF_3') | ~l1_pre_topc(A_350) | ~v2_pre_topc(A_350) | v2_struct_0(A_350))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_58, c_56, c_196, c_588])).
% 16.17/7.85  tff(c_600, plain, (![D_352, A_353]: (k7_relat_1('#skF_6', u1_struct_0(D_352))=k3_tmap_1(A_353, '#skF_3', '#skF_5', D_352, '#skF_6') | ~m1_pre_topc(D_352, '#skF_5') | ~m1_pre_topc(D_352, A_353) | ~m1_pre_topc('#skF_5', A_353) | ~l1_pre_topc(A_353) | ~v2_pre_topc(A_353) | v2_struct_0(A_353))), inference(negUnitSimplification, [status(thm)], [c_72, c_594])).
% 16.17/7.85  tff(c_604, plain, (k7_relat_1('#skF_6', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6') | ~m1_pre_topc('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_64, c_600])).
% 16.17/7.85  tff(c_612, plain, (k7_relat_1('#skF_6', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_60, c_52, c_604])).
% 16.17/7.85  tff(c_613, plain, (k7_relat_1('#skF_6', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_78, c_612])).
% 16.17/7.85  tff(c_606, plain, (k7_relat_1('#skF_6', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_5', '#skF_3', '#skF_5', '#skF_4', '#skF_6') | ~m1_pre_topc('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_5') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_52, c_600])).
% 16.17/7.85  tff(c_616, plain, (k7_relat_1('#skF_6', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_5', '#skF_3', '#skF_5', '#skF_4', '#skF_6') | ~m1_pre_topc('#skF_5', '#skF_5') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_144, c_102, c_52, c_606])).
% 16.17/7.85  tff(c_617, plain, (k7_relat_1('#skF_6', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_5', '#skF_3', '#skF_5', '#skF_4', '#skF_6') | ~m1_pre_topc('#skF_5', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_62, c_616])).
% 16.17/7.85  tff(c_631, plain, (k3_tmap_1('#skF_5', '#skF_3', '#skF_5', '#skF_4', '#skF_6')=k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6') | ~m1_pre_topc('#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_613, c_617])).
% 16.17/7.85  tff(c_632, plain, (~m1_pre_topc('#skF_5', '#skF_5')), inference(splitLeft, [status(thm)], [c_631])).
% 16.17/7.85  tff(c_636, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_40, c_632])).
% 16.17/7.85  tff(c_640, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_102, c_636])).
% 16.17/7.85  tff(c_642, plain, (m1_pre_topc('#skF_5', '#skF_5')), inference(splitRight, [status(thm)], [c_631])).
% 16.17/7.85  tff(c_641, plain, (k3_tmap_1('#skF_5', '#skF_3', '#skF_5', '#skF_4', '#skF_6')=k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6')), inference(splitRight, [status(thm)], [c_631])).
% 16.17/7.85  tff(c_405, plain, (![A_274, B_275, D_271, E_273, C_272]: (v1_funct_1(k3_tmap_1(A_274, B_275, C_272, D_271, E_273)) | ~m1_subset_1(E_273, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_272), u1_struct_0(B_275)))) | ~v1_funct_2(E_273, u1_struct_0(C_272), u1_struct_0(B_275)) | ~v1_funct_1(E_273) | ~m1_pre_topc(D_271, A_274) | ~m1_pre_topc(C_272, A_274) | ~l1_pre_topc(B_275) | ~v2_pre_topc(B_275) | v2_struct_0(B_275) | ~l1_pre_topc(A_274) | ~v2_pre_topc(A_274) | v2_struct_0(A_274))), inference(cnfTransformation, [status(thm)], [f_185])).
% 16.17/7.85  tff(c_407, plain, (![A_274, D_271]: (v1_funct_1(k3_tmap_1(A_274, '#skF_3', '#skF_5', D_271, '#skF_6')) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_6') | ~m1_pre_topc(D_271, A_274) | ~m1_pre_topc('#skF_5', A_274) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc(A_274) | ~v2_pre_topc(A_274) | v2_struct_0(A_274))), inference(resolution, [status(thm)], [c_54, c_405])).
% 16.17/7.85  tff(c_412, plain, (![A_274, D_271]: (v1_funct_1(k3_tmap_1(A_274, '#skF_3', '#skF_5', D_271, '#skF_6')) | ~m1_pre_topc(D_271, A_274) | ~m1_pre_topc('#skF_5', A_274) | v2_struct_0('#skF_3') | ~l1_pre_topc(A_274) | ~v2_pre_topc(A_274) | v2_struct_0(A_274))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_58, c_56, c_407])).
% 16.17/7.85  tff(c_413, plain, (![A_274, D_271]: (v1_funct_1(k3_tmap_1(A_274, '#skF_3', '#skF_5', D_271, '#skF_6')) | ~m1_pre_topc(D_271, A_274) | ~m1_pre_topc('#skF_5', A_274) | ~l1_pre_topc(A_274) | ~v2_pre_topc(A_274) | v2_struct_0(A_274))), inference(negUnitSimplification, [status(thm)], [c_72, c_412])).
% 16.17/7.85  tff(c_690, plain, (v1_funct_1(k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6')) | ~m1_pre_topc('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_5') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_641, c_413])).
% 16.17/7.85  tff(c_706, plain, (v1_funct_1(k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_144, c_102, c_642, c_52, c_690])).
% 16.17/7.85  tff(c_707, plain, (v1_funct_1(k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_62, c_706])).
% 16.17/7.85  tff(c_496, plain, (![A_312, D_309, C_310, E_311, B_313]: (v1_funct_2(k3_tmap_1(A_312, B_313, C_310, D_309, E_311), u1_struct_0(D_309), u1_struct_0(B_313)) | ~m1_subset_1(E_311, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_310), u1_struct_0(B_313)))) | ~v1_funct_2(E_311, u1_struct_0(C_310), u1_struct_0(B_313)) | ~v1_funct_1(E_311) | ~m1_pre_topc(D_309, A_312) | ~m1_pre_topc(C_310, A_312) | ~l1_pre_topc(B_313) | ~v2_pre_topc(B_313) | v2_struct_0(B_313) | ~l1_pre_topc(A_312) | ~v2_pre_topc(A_312) | v2_struct_0(A_312))), inference(cnfTransformation, [status(thm)], [f_185])).
% 16.17/7.85  tff(c_498, plain, (![A_312, D_309]: (v1_funct_2(k3_tmap_1(A_312, '#skF_3', '#skF_5', D_309, '#skF_6'), u1_struct_0(D_309), u1_struct_0('#skF_3')) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_6') | ~m1_pre_topc(D_309, A_312) | ~m1_pre_topc('#skF_5', A_312) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc(A_312) | ~v2_pre_topc(A_312) | v2_struct_0(A_312))), inference(resolution, [status(thm)], [c_54, c_496])).
% 16.17/7.85  tff(c_503, plain, (![A_312, D_309]: (v1_funct_2(k3_tmap_1(A_312, '#skF_3', '#skF_5', D_309, '#skF_6'), u1_struct_0(D_309), u1_struct_0('#skF_3')) | ~m1_pre_topc(D_309, A_312) | ~m1_pre_topc('#skF_5', A_312) | v2_struct_0('#skF_3') | ~l1_pre_topc(A_312) | ~v2_pre_topc(A_312) | v2_struct_0(A_312))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_58, c_56, c_498])).
% 16.17/7.85  tff(c_504, plain, (![A_312, D_309]: (v1_funct_2(k3_tmap_1(A_312, '#skF_3', '#skF_5', D_309, '#skF_6'), u1_struct_0(D_309), u1_struct_0('#skF_3')) | ~m1_pre_topc(D_309, A_312) | ~m1_pre_topc('#skF_5', A_312) | ~l1_pre_topc(A_312) | ~v2_pre_topc(A_312) | v2_struct_0(A_312))), inference(negUnitSimplification, [status(thm)], [c_72, c_503])).
% 16.17/7.85  tff(c_687, plain, (v1_funct_2(k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6'), u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~m1_pre_topc('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_5') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_641, c_504])).
% 16.17/7.85  tff(c_703, plain, (v1_funct_2(k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6'), u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_144, c_102, c_642, c_52, c_687])).
% 16.17/7.85  tff(c_704, plain, (v1_funct_2(k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6'), u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_62, c_703])).
% 16.17/7.85  tff(c_32, plain, (![A_74, D_77, B_75, C_76, E_78]: (m1_subset_1(k3_tmap_1(A_74, B_75, C_76, D_77, E_78), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_77), u1_struct_0(B_75)))) | ~m1_subset_1(E_78, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_76), u1_struct_0(B_75)))) | ~v1_funct_2(E_78, u1_struct_0(C_76), u1_struct_0(B_75)) | ~v1_funct_1(E_78) | ~m1_pre_topc(D_77, A_74) | ~m1_pre_topc(C_76, A_74) | ~l1_pre_topc(B_75) | ~v2_pre_topc(B_75) | v2_struct_0(B_75) | ~l1_pre_topc(A_74) | ~v2_pre_topc(A_74) | v2_struct_0(A_74))), inference(cnfTransformation, [status(thm)], [f_185])).
% 16.17/7.85  tff(c_684, plain, (m1_subset_1(k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_6') | ~m1_pre_topc('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_5') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_641, c_32])).
% 16.17/7.85  tff(c_700, plain, (m1_subset_1(k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))) | v2_struct_0('#skF_3') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_144, c_102, c_70, c_68, c_642, c_52, c_58, c_56, c_54, c_684])).
% 16.17/7.85  tff(c_701, plain, (m1_subset_1(k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_62, c_72, c_700])).
% 16.17/7.85  tff(c_50, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_249])).
% 16.17/7.85  tff(c_48, plain, (v1_funct_2('#skF_7', u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_249])).
% 16.17/7.85  tff(c_46, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_249])).
% 16.17/7.85  tff(c_278, plain, (![A_249, B_250, C_251, D_252]: (m1_subset_1('#skF_1'(A_249, B_250, C_251, D_252), A_249) | r2_funct_2(A_249, B_250, C_251, D_252) | ~m1_subset_1(D_252, k1_zfmisc_1(k2_zfmisc_1(A_249, B_250))) | ~v1_funct_2(D_252, A_249, B_250) | ~v1_funct_1(D_252) | ~m1_subset_1(C_251, k1_zfmisc_1(k2_zfmisc_1(A_249, B_250))) | ~v1_funct_2(C_251, A_249, B_250) | ~v1_funct_1(C_251))), inference(cnfTransformation, [status(thm)], [f_76])).
% 16.17/7.85  tff(c_282, plain, (![C_251]: (m1_subset_1('#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), C_251, '#skF_7'), u1_struct_0('#skF_4')) | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), C_251, '#skF_7') | ~v1_funct_2('#skF_7', u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_7') | ~m1_subset_1(C_251, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))) | ~v1_funct_2(C_251, u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1(C_251))), inference(resolution, [status(thm)], [c_46, c_278])).
% 16.17/7.85  tff(c_288, plain, (![C_251]: (m1_subset_1('#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), C_251, '#skF_7'), u1_struct_0('#skF_4')) | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), C_251, '#skF_7') | ~m1_subset_1(C_251, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))) | ~v1_funct_2(C_251, u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1(C_251))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_282])).
% 16.17/7.85  tff(c_88, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_64, c_82])).
% 16.17/7.85  tff(c_98, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_88])).
% 16.17/7.85  tff(c_24, plain, (![A_38]: (l1_struct_0(A_38) | ~l1_pre_topc(A_38))), inference(cnfTransformation, [status(thm)], [f_108])).
% 16.17/7.85  tff(c_66, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_249])).
% 16.17/7.85  tff(c_2, plain, (![A_1, B_2]: (r2_hidden(A_1, B_2) | v1_xboole_0(B_2) | ~m1_subset_1(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 16.17/7.85  tff(c_167, plain, (![B_225, A_226]: (m1_subset_1(u1_struct_0(B_225), k1_zfmisc_1(u1_struct_0(A_226))) | ~m1_pre_topc(B_225, A_226) | ~l1_pre_topc(A_226))), inference(cnfTransformation, [status(thm)], [f_192])).
% 16.17/7.85  tff(c_4, plain, (![A_3, C_5, B_4]: (m1_subset_1(A_3, C_5) | ~m1_subset_1(B_4, k1_zfmisc_1(C_5)) | ~r2_hidden(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 16.17/7.85  tff(c_175, plain, (![A_230, A_231, B_232]: (m1_subset_1(A_230, u1_struct_0(A_231)) | ~r2_hidden(A_230, u1_struct_0(B_232)) | ~m1_pre_topc(B_232, A_231) | ~l1_pre_topc(A_231))), inference(resolution, [status(thm)], [c_167, c_4])).
% 16.17/7.85  tff(c_238, plain, (![A_246, A_247, B_248]: (m1_subset_1(A_246, u1_struct_0(A_247)) | ~m1_pre_topc(B_248, A_247) | ~l1_pre_topc(A_247) | v1_xboole_0(u1_struct_0(B_248)) | ~m1_subset_1(A_246, u1_struct_0(B_248)))), inference(resolution, [status(thm)], [c_2, c_175])).
% 16.17/7.85  tff(c_242, plain, (![A_246]: (m1_subset_1(A_246, u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | v1_xboole_0(u1_struct_0('#skF_4')) | ~m1_subset_1(A_246, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_64, c_238])).
% 16.17/7.85  tff(c_250, plain, (![A_246]: (m1_subset_1(A_246, u1_struct_0('#skF_2')) | v1_xboole_0(u1_struct_0('#skF_4')) | ~m1_subset_1(A_246, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_242])).
% 16.17/7.85  tff(c_257, plain, (v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_250])).
% 16.17/7.85  tff(c_28, plain, (![A_42]: (~v1_xboole_0(u1_struct_0(A_42)) | ~l1_struct_0(A_42) | v2_struct_0(A_42))), inference(cnfTransformation, [status(thm)], [f_123])).
% 16.17/7.85  tff(c_262, plain, (~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_257, c_28])).
% 16.17/7.85  tff(c_268, plain, (~l1_struct_0('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_66, c_262])).
% 16.17/7.85  tff(c_271, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_24, c_268])).
% 16.17/7.85  tff(c_275, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_98, c_271])).
% 16.17/7.85  tff(c_277, plain, (~v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_250])).
% 16.17/7.85  tff(c_434, plain, (![C_281]: (m1_subset_1('#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), C_281, '#skF_7'), u1_struct_0('#skF_4')) | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), C_281, '#skF_7') | ~m1_subset_1(C_281, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))) | ~v1_funct_2(C_281, u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1(C_281))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_282])).
% 16.17/7.85  tff(c_244, plain, (![A_246]: (m1_subset_1(A_246, u1_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5') | v1_xboole_0(u1_struct_0('#skF_4')) | ~m1_subset_1(A_246, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_52, c_238])).
% 16.17/7.85  tff(c_253, plain, (![A_246]: (m1_subset_1(A_246, u1_struct_0('#skF_5')) | v1_xboole_0(u1_struct_0('#skF_4')) | ~m1_subset_1(A_246, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_102, c_244])).
% 16.17/7.85  tff(c_315, plain, (![A_246]: (m1_subset_1(A_246, u1_struct_0('#skF_5')) | ~m1_subset_1(A_246, u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_277, c_253])).
% 16.17/7.85  tff(c_246, plain, (![A_246]: (m1_subset_1(A_246, u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | v1_xboole_0(u1_struct_0('#skF_5')) | ~m1_subset_1(A_246, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_60, c_238])).
% 16.17/7.85  tff(c_256, plain, (![A_246]: (m1_subset_1(A_246, u1_struct_0('#skF_2')) | v1_xboole_0(u1_struct_0('#skF_5')) | ~m1_subset_1(A_246, u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_246])).
% 16.17/7.85  tff(c_293, plain, (v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitLeft, [status(thm)], [c_256])).
% 16.17/7.85  tff(c_298, plain, (~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_293, c_28])).
% 16.17/7.85  tff(c_304, plain, (~l1_struct_0('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_62, c_298])).
% 16.17/7.85  tff(c_307, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_24, c_304])).
% 16.17/7.85  tff(c_311, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_102, c_307])).
% 16.17/7.85  tff(c_313, plain, (~v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_256])).
% 16.17/7.85  tff(c_316, plain, (![A_255]: (m1_subset_1(A_255, u1_struct_0('#skF_5')) | ~m1_subset_1(A_255, u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_277, c_253])).
% 16.17/7.85  tff(c_20, plain, (![A_31, B_32, C_33, D_34]: (k3_funct_2(A_31, B_32, C_33, D_34)=k1_funct_1(C_33, D_34) | ~m1_subset_1(D_34, A_31) | ~m1_subset_1(C_33, k1_zfmisc_1(k2_zfmisc_1(A_31, B_32))) | ~v1_funct_2(C_33, A_31, B_32) | ~v1_funct_1(C_33) | v1_xboole_0(A_31))), inference(cnfTransformation, [status(thm)], [f_95])).
% 16.17/7.85  tff(c_321, plain, (![B_32, C_33, A_255]: (k3_funct_2(u1_struct_0('#skF_5'), B_32, C_33, A_255)=k1_funct_1(C_33, A_255) | ~m1_subset_1(C_33, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), B_32))) | ~v1_funct_2(C_33, u1_struct_0('#skF_5'), B_32) | ~v1_funct_1(C_33) | v1_xboole_0(u1_struct_0('#skF_5')) | ~m1_subset_1(A_255, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_316, c_20])).
% 16.17/7.85  tff(c_326, plain, (![B_256, C_257, A_258]: (k3_funct_2(u1_struct_0('#skF_5'), B_256, C_257, A_258)=k1_funct_1(C_257, A_258) | ~m1_subset_1(C_257, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), B_256))) | ~v1_funct_2(C_257, u1_struct_0('#skF_5'), B_256) | ~v1_funct_1(C_257) | ~m1_subset_1(A_258, u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_313, c_321])).
% 16.17/7.85  tff(c_328, plain, (![A_258]: (k3_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', A_258)=k1_funct_1('#skF_6', A_258) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_6') | ~m1_subset_1(A_258, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_54, c_326])).
% 16.17/7.85  tff(c_332, plain, (![A_259]: (k3_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', A_259)=k1_funct_1('#skF_6', A_259) | ~m1_subset_1(A_259, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_328])).
% 16.17/7.85  tff(c_44, plain, (![G_203]: (k3_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', G_203)=k1_funct_1('#skF_7', G_203) | ~r2_hidden(G_203, u1_struct_0('#skF_4')) | ~m1_subset_1(G_203, u1_struct_0('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_249])).
% 16.17/7.85  tff(c_369, plain, (![A_265]: (k1_funct_1('#skF_7', A_265)=k1_funct_1('#skF_6', A_265) | ~r2_hidden(A_265, u1_struct_0('#skF_4')) | ~m1_subset_1(A_265, u1_struct_0('#skF_5')) | ~m1_subset_1(A_265, u1_struct_0('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_332, c_44])).
% 16.17/7.85  tff(c_373, plain, (![A_1]: (k1_funct_1('#skF_7', A_1)=k1_funct_1('#skF_6', A_1) | ~m1_subset_1(A_1, u1_struct_0('#skF_5')) | v1_xboole_0(u1_struct_0('#skF_4')) | ~m1_subset_1(A_1, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_2, c_369])).
% 16.17/7.85  tff(c_377, plain, (![A_266]: (k1_funct_1('#skF_7', A_266)=k1_funct_1('#skF_6', A_266) | ~m1_subset_1(A_266, u1_struct_0('#skF_5')) | ~m1_subset_1(A_266, u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_277, c_373])).
% 16.17/7.85  tff(c_381, plain, (![A_246]: (k1_funct_1('#skF_7', A_246)=k1_funct_1('#skF_6', A_246) | ~m1_subset_1(A_246, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_315, c_377])).
% 16.17/7.85  tff(c_442, plain, (![C_281]: (k1_funct_1('#skF_7', '#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), C_281, '#skF_7'))=k1_funct_1('#skF_6', '#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), C_281, '#skF_7')) | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), C_281, '#skF_7') | ~m1_subset_1(C_281, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))) | ~v1_funct_2(C_281, u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1(C_281))), inference(resolution, [status(thm)], [c_434, c_381])).
% 16.17/7.85  tff(c_911, plain, (k1_funct_1('#skF_7', '#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6'), '#skF_7'))=k1_funct_1('#skF_6', '#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6'), '#skF_7')) | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6'), '#skF_7') | ~v1_funct_2(k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6'), u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1(k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6'))), inference(resolution, [status(thm)], [c_701, c_442])).
% 16.17/7.85  tff(c_945, plain, (k1_funct_1('#skF_7', '#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6'), '#skF_7'))=k1_funct_1('#skF_6', '#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6'), '#skF_7')) | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_707, c_704, c_911])).
% 16.17/7.85  tff(c_946, plain, (k1_funct_1('#skF_7', '#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6'), '#skF_7'))=k1_funct_1('#skF_6', '#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6'), '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_42, c_945])).
% 16.17/7.85  tff(c_10, plain, (![C_14, A_12, B_13]: (v1_relat_1(C_14) | ~m1_subset_1(C_14, k1_zfmisc_1(k2_zfmisc_1(A_12, B_13))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 16.17/7.85  tff(c_114, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_54, c_10])).
% 16.17/7.85  tff(c_8, plain, (![C_11, B_10, A_9]: (k1_funct_1(k7_relat_1(C_11, B_10), A_9)=k1_funct_1(C_11, A_9) | ~r2_hidden(A_9, B_10) | ~v1_funct_1(C_11) | ~v1_relat_1(C_11))), inference(cnfTransformation, [status(thm)], [f_52])).
% 16.17/7.85  tff(c_461, plain, (![D_289, A_290, B_291, C_292]: (k1_funct_1(D_289, '#skF_1'(A_290, B_291, C_292, D_289))!=k1_funct_1(C_292, '#skF_1'(A_290, B_291, C_292, D_289)) | r2_funct_2(A_290, B_291, C_292, D_289) | ~m1_subset_1(D_289, k1_zfmisc_1(k2_zfmisc_1(A_290, B_291))) | ~v1_funct_2(D_289, A_290, B_291) | ~v1_funct_1(D_289) | ~m1_subset_1(C_292, k1_zfmisc_1(k2_zfmisc_1(A_290, B_291))) | ~v1_funct_2(C_292, A_290, B_291) | ~v1_funct_1(C_292))), inference(cnfTransformation, [status(thm)], [f_76])).
% 16.17/7.85  tff(c_1274, plain, (![D_394, B_391, C_392, A_393, B_390]: (k1_funct_1(D_394, '#skF_1'(A_393, B_390, k7_relat_1(C_392, B_391), D_394))!=k1_funct_1(C_392, '#skF_1'(A_393, B_390, k7_relat_1(C_392, B_391), D_394)) | r2_funct_2(A_393, B_390, k7_relat_1(C_392, B_391), D_394) | ~m1_subset_1(D_394, k1_zfmisc_1(k2_zfmisc_1(A_393, B_390))) | ~v1_funct_2(D_394, A_393, B_390) | ~v1_funct_1(D_394) | ~m1_subset_1(k7_relat_1(C_392, B_391), k1_zfmisc_1(k2_zfmisc_1(A_393, B_390))) | ~v1_funct_2(k7_relat_1(C_392, B_391), A_393, B_390) | ~v1_funct_1(k7_relat_1(C_392, B_391)) | ~r2_hidden('#skF_1'(A_393, B_390, k7_relat_1(C_392, B_391), D_394), B_391) | ~v1_funct_1(C_392) | ~v1_relat_1(C_392))), inference(superposition, [status(thm), theory('equality')], [c_8, c_461])).
% 16.17/7.85  tff(c_1284, plain, (![D_394, A_393, B_390]: (k1_funct_1(D_394, '#skF_1'(A_393, B_390, k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6'), D_394))!=k1_funct_1('#skF_6', '#skF_1'(A_393, B_390, k7_relat_1('#skF_6', u1_struct_0('#skF_4')), D_394)) | r2_funct_2(A_393, B_390, k7_relat_1('#skF_6', u1_struct_0('#skF_4')), D_394) | ~m1_subset_1(D_394, k1_zfmisc_1(k2_zfmisc_1(A_393, B_390))) | ~v1_funct_2(D_394, A_393, B_390) | ~v1_funct_1(D_394) | ~m1_subset_1(k7_relat_1('#skF_6', u1_struct_0('#skF_4')), k1_zfmisc_1(k2_zfmisc_1(A_393, B_390))) | ~v1_funct_2(k7_relat_1('#skF_6', u1_struct_0('#skF_4')), A_393, B_390) | ~v1_funct_1(k7_relat_1('#skF_6', u1_struct_0('#skF_4'))) | ~r2_hidden('#skF_1'(A_393, B_390, k7_relat_1('#skF_6', u1_struct_0('#skF_4')), D_394), u1_struct_0('#skF_4')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_613, c_1274])).
% 16.17/7.85  tff(c_15967, plain, (![D_1203, A_1204, B_1205]: (k1_funct_1(D_1203, '#skF_1'(A_1204, B_1205, k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6'), D_1203))!=k1_funct_1('#skF_6', '#skF_1'(A_1204, B_1205, k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6'), D_1203)) | r2_funct_2(A_1204, B_1205, k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6'), D_1203) | ~m1_subset_1(D_1203, k1_zfmisc_1(k2_zfmisc_1(A_1204, B_1205))) | ~v1_funct_2(D_1203, A_1204, B_1205) | ~v1_funct_1(D_1203) | ~m1_subset_1(k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(A_1204, B_1205))) | ~v1_funct_2(k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6'), A_1204, B_1205) | ~r2_hidden('#skF_1'(A_1204, B_1205, k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6'), D_1203), u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_114, c_58, c_613, c_707, c_613, c_613, c_613, c_613, c_613, c_1284])).
% 16.17/7.85  tff(c_16017, plain, (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6'), '#skF_7') | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_7', u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_7') | ~m1_subset_1(k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))) | ~v1_funct_2(k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6'), u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~r2_hidden('#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6'), '#skF_7'), u1_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_946, c_15967])).
% 16.17/7.85  tff(c_16033, plain, (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6'), '#skF_7') | ~r2_hidden('#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6'), '#skF_7'), u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_704, c_701, c_50, c_48, c_46, c_16017])).
% 16.17/7.85  tff(c_16034, plain, (~r2_hidden('#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6'), '#skF_7'), u1_struct_0('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_42, c_16033])).
% 16.17/7.85  tff(c_16037, plain, (v1_xboole_0(u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6'), '#skF_7'), u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_2, c_16034])).
% 16.17/7.85  tff(c_16040, plain, (~m1_subset_1('#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6'), '#skF_7'), u1_struct_0('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_277, c_16037])).
% 16.17/7.85  tff(c_16043, plain, (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6'), '#skF_7') | ~m1_subset_1(k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))) | ~v1_funct_2(k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6'), u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1(k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6'))), inference(resolution, [status(thm)], [c_288, c_16040])).
% 16.17/7.85  tff(c_16046, plain, (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_707, c_704, c_701, c_16043])).
% 16.17/7.85  tff(c_16048, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_16046])).
% 16.17/7.85  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 16.17/7.85  
% 16.17/7.85  Inference rules
% 16.17/7.85  ----------------------
% 16.17/7.85  #Ref     : 7
% 16.17/7.85  #Sup     : 3101
% 16.17/7.85  #Fact    : 0
% 16.17/7.85  #Define  : 0
% 16.17/7.85  #Split   : 32
% 16.17/7.85  #Chain   : 0
% 16.17/7.85  #Close   : 0
% 16.17/7.85  
% 16.17/7.85  Ordering : KBO
% 16.17/7.85  
% 16.17/7.85  Simplification rules
% 16.17/7.85  ----------------------
% 16.17/7.85  #Subsume      : 548
% 16.17/7.85  #Demod        : 8307
% 16.17/7.85  #Tautology    : 517
% 16.17/7.85  #SimpNegUnit  : 1283
% 16.17/7.85  #BackRed      : 1
% 16.17/7.85  
% 16.17/7.85  #Partial instantiations: 0
% 16.17/7.85  #Strategies tried      : 1
% 16.17/7.85  
% 16.17/7.85  Timing (in seconds)
% 16.17/7.85  ----------------------
% 16.17/7.85  Preprocessing        : 0.44
% 16.17/7.85  Parsing              : 0.23
% 16.17/7.85  CNF conversion       : 0.05
% 16.17/7.85  Main loop            : 6.61
% 16.17/7.85  Inferencing          : 1.78
% 16.17/7.85  Reduction            : 2.66
% 16.17/7.85  Demodulation         : 2.15
% 16.17/7.85  BG Simplification    : 0.15
% 16.17/7.85  Subsumption          : 1.77
% 16.17/7.85  Abstraction          : 0.29
% 16.17/7.85  MUC search           : 0.00
% 16.17/7.85  Cooper               : 0.00
% 16.17/7.85  Total                : 7.11
% 16.17/7.85  Index Insertion      : 0.00
% 16.17/7.85  Index Deletion       : 0.00
% 16.17/7.85  Index Matching       : 0.00
% 16.17/7.85  BG Taut test         : 0.00
%------------------------------------------------------------------------------
