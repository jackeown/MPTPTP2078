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
% DateTime   : Thu Dec  3 10:27:42 EST 2020

% Result     : Theorem 14.01s
% Output     : CNFRefutation 14.01s
% Verified   : 
% Statistics : Number of formulae       :  156 (1760 expanded)
%              Number of leaves         :   42 ( 625 expanded)
%              Depth                    :   19
%              Number of atoms          :  445 (8364 expanded)
%              Number of equality atoms :   31 ( 951 expanded)
%              Maximal formula depth    :   26 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > v3_pre_topc > v1_tsep_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k2_partfun1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k3_tmap_1,type,(
    k3_tmap_1: ( $i * $i * $i * $i * $i ) > $i )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(g1_pre_topc,type,(
    g1_pre_topc: ( $i * $i ) > $i )).

tff(r1_tmap_1,type,(
    r1_tmap_1: ( $i * $i * $i * $i ) > $o )).

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

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff(v1_tsep_1,type,(
    v1_tsep_1: ( $i * $i ) > $o )).

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

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_262,negated_conjecture,(
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
                       => ( g1_pre_topc(u1_struct_0(C),u1_pre_topc(C)) = D
                         => ! [F] :
                              ( m1_subset_1(F,u1_struct_0(D))
                             => ! [G] :
                                  ( m1_subset_1(G,u1_struct_0(C))
                                 => ( ( F = G
                                      & r1_tmap_1(C,B,k3_tmap_1(A,B,D,C,E),G) )
                                   => r1_tmap_1(D,B,E,F) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_tmap_1)).

tff(f_34,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_49,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_42,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_38,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_145,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_149,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_58,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ( m1_pre_topc(A,B)
          <=> m1_pre_topc(A,g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_pre_topc)).

tff(f_64,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v3_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_tops_1)).

tff(f_138,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( C = u1_struct_0(B)
               => ( ( v1_tsep_1(B,A)
                    & m1_pre_topc(B,A) )
                <=> v3_pre_topc(C,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_tsep_1)).

tff(f_120,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( v2_pre_topc(B)
            & l1_pre_topc(B) )
         => ! [C] :
              ( ( v2_pre_topc(C)
                & l1_pre_topc(C) )
             => ( C = g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))
               => ( ( v1_tsep_1(B,A)
                    & m1_pre_topc(B,A) )
                <=> ( v1_tsep_1(C,A)
                    & m1_pre_topc(C,A) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_tmap_1)).

tff(f_96,axiom,(
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

tff(f_213,axiom,(
    ! [A] :
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
                  ( ( ~ v2_struct_0(D)
                    & m1_pre_topc(D,B) )
                 => ! [E] :
                      ( ( v1_funct_1(E)
                        & v1_funct_2(E,u1_struct_0(D),u1_struct_0(A))
                        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D),u1_struct_0(A)))) )
                     => ( ( v1_tsep_1(C,B)
                          & m1_pre_topc(C,B)
                          & m1_pre_topc(C,D) )
                       => ! [F] :
                            ( m1_subset_1(F,u1_struct_0(D))
                           => ! [G] :
                                ( m1_subset_1(G,u1_struct_0(C))
                               => ( F = G
                                 => ( r1_tmap_1(D,A,E,F)
                                  <=> r1_tmap_1(C,A,k3_tmap_1(B,A,D,C,E),G) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_tmap_1)).

tff(c_72,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_262])).

tff(c_62,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_262])).

tff(c_66,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_262])).

tff(c_42,plain,(
    ~ r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_262])).

tff(c_70,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_262])).

tff(c_68,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_262])).

tff(c_76,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_262])).

tff(c_74,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_262])).

tff(c_60,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_262])).

tff(c_157,plain,(
    ! [B_323,A_324] :
      ( v2_pre_topc(B_323)
      | ~ m1_pre_topc(B_323,A_324)
      | ~ l1_pre_topc(A_324)
      | ~ v2_pre_topc(A_324) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_166,plain,
    ( v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_60,c_157])).

tff(c_173,plain,(
    v2_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_166])).

tff(c_115,plain,(
    ! [B_320,A_321] :
      ( l1_pre_topc(B_320)
      | ~ m1_pre_topc(B_320,A_321)
      | ~ l1_pre_topc(A_321) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_124,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_60,c_115])).

tff(c_131,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_124])).

tff(c_64,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_262])).

tff(c_121,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_64,c_115])).

tff(c_128,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_121])).

tff(c_6,plain,(
    ! [A_5] :
      ( l1_struct_0(A_5)
      | ~ l1_pre_topc(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_91,plain,(
    ! [A_318] :
      ( u1_struct_0(A_318) = k2_struct_0(A_318)
      | ~ l1_struct_0(A_318) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_95,plain,(
    ! [A_5] :
      ( u1_struct_0(A_5) = k2_struct_0(A_5)
      | ~ l1_pre_topc(A_5) ) ),
    inference(resolution,[status(thm)],[c_6,c_91])).

tff(c_135,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_128,c_95])).

tff(c_139,plain,(
    u1_struct_0('#skF_4') = k2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_131,c_95])).

tff(c_175,plain,(
    ! [B_325,A_326] :
      ( m1_subset_1(u1_struct_0(B_325),k1_zfmisc_1(u1_struct_0(A_326)))
      | ~ m1_pre_topc(B_325,A_326)
      | ~ l1_pre_topc(A_326) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_181,plain,(
    ! [B_325] :
      ( m1_subset_1(u1_struct_0(B_325),k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ m1_pre_topc(B_325,'#skF_4')
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_139,c_175])).

tff(c_208,plain,(
    ! [B_327] :
      ( m1_subset_1(u1_struct_0(B_327),k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ m1_pre_topc(B_327,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_181])).

tff(c_214,plain,
    ( m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_4')))
    | ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_208])).

tff(c_370,plain,(
    ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_214])).

tff(c_34,plain,(
    ! [A_61] :
      ( m1_pre_topc(A_61,A_61)
      | ~ l1_pre_topc(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_187,plain,(
    ! [B_325] :
      ( m1_subset_1(u1_struct_0(B_325),k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ m1_pre_topc(B_325,'#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_175])).

tff(c_221,plain,(
    ! [B_328] :
      ( m1_subset_1(u1_struct_0(B_328),k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ m1_pre_topc(B_328,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_187])).

tff(c_227,plain,
    ( m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_3')))
    | ~ m1_pre_topc('#skF_3','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_221])).

tff(c_274,plain,(
    ~ m1_pre_topc('#skF_3','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_227])).

tff(c_294,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_274])).

tff(c_301,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_294])).

tff(c_303,plain,(
    m1_pre_topc('#skF_3','#skF_3') ),
    inference(splitRight,[status(thm)],[c_227])).

tff(c_52,plain,(
    g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_262])).

tff(c_140,plain,(
    g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_52])).

tff(c_388,plain,(
    ! [A_340,B_341] :
      ( m1_pre_topc(A_340,g1_pre_topc(u1_struct_0(B_341),u1_pre_topc(B_341)))
      | ~ m1_pre_topc(A_340,B_341)
      | ~ l1_pre_topc(B_341)
      | ~ l1_pre_topc(A_340) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_409,plain,(
    ! [A_340] :
      ( m1_pre_topc(A_340,g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ m1_pre_topc(A_340,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ l1_pre_topc(A_340) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_388])).

tff(c_431,plain,(
    ! [A_342] :
      ( m1_pre_topc(A_342,'#skF_4')
      | ~ m1_pre_topc(A_342,'#skF_3')
      | ~ l1_pre_topc(A_342) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_140,c_409])).

tff(c_437,plain,
    ( m1_pre_topc('#skF_3','#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_303,c_431])).

tff(c_445,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_437])).

tff(c_447,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_370,c_445])).

tff(c_449,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_214])).

tff(c_211,plain,
    ( m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_4')))
    | ~ m1_pre_topc('#skF_4','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_139,c_208])).

tff(c_681,plain,(
    ~ m1_pre_topc('#skF_4','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_211])).

tff(c_684,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_681])).

tff(c_688,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_684])).

tff(c_690,plain,(
    m1_pre_topc('#skF_4','#skF_4') ),
    inference(splitRight,[status(thm)],[c_211])).

tff(c_58,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_262])).

tff(c_96,plain,(
    ! [A_319] :
      ( u1_struct_0(A_319) = k2_struct_0(A_319)
      | ~ l1_pre_topc(A_319) ) ),
    inference(resolution,[status(thm)],[c_6,c_91])).

tff(c_104,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_96])).

tff(c_56,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_262])).

tff(c_110,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_56])).

tff(c_150,plain,(
    v1_funct_2('#skF_5',k2_struct_0('#skF_4'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_110])).

tff(c_54,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_262])).

tff(c_109,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_54])).

tff(c_174,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_109])).

tff(c_14,plain,(
    ! [A_12] :
      ( v3_pre_topc(k2_struct_0(A_12),A_12)
      | ~ l1_pre_topc(A_12)
      | ~ v2_pre_topc(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_32,plain,(
    ! [B_60,A_58] :
      ( m1_subset_1(u1_struct_0(B_60),k1_zfmisc_1(u1_struct_0(A_58)))
      | ~ m1_pre_topc(B_60,A_58)
      | ~ l1_pre_topc(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_640,plain,(
    ! [B_348,A_349] :
      ( v1_tsep_1(B_348,A_349)
      | ~ v3_pre_topc(u1_struct_0(B_348),A_349)
      | ~ m1_subset_1(u1_struct_0(B_348),k1_zfmisc_1(u1_struct_0(A_349)))
      | ~ m1_pre_topc(B_348,A_349)
      | ~ l1_pre_topc(A_349)
      | ~ v2_pre_topc(A_349) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_1726,plain,(
    ! [B_414,A_415] :
      ( v1_tsep_1(B_414,A_415)
      | ~ v3_pre_topc(u1_struct_0(B_414),A_415)
      | ~ v2_pre_topc(A_415)
      | ~ m1_pre_topc(B_414,A_415)
      | ~ l1_pre_topc(A_415) ) ),
    inference(resolution,[status(thm)],[c_32,c_640])).

tff(c_1827,plain,(
    ! [A_433] :
      ( v1_tsep_1('#skF_4',A_433)
      | ~ v3_pre_topc(k2_struct_0('#skF_4'),A_433)
      | ~ v2_pre_topc(A_433)
      | ~ m1_pre_topc('#skF_4',A_433)
      | ~ l1_pre_topc(A_433) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_139,c_1726])).

tff(c_1834,plain,
    ( v1_tsep_1('#skF_4','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_14,c_1827])).

tff(c_1838,plain,(
    v1_tsep_1('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_131,c_690,c_1834])).

tff(c_163,plain,
    ( v2_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_64,c_157])).

tff(c_170,plain,(
    v2_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_163])).

tff(c_1296,plain,(
    ! [B_371,A_372] :
      ( v1_tsep_1(B_371,A_372)
      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(B_371),u1_pre_topc(B_371)),A_372)
      | ~ v1_tsep_1(g1_pre_topc(u1_struct_0(B_371),u1_pre_topc(B_371)),A_372)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(B_371),u1_pre_topc(B_371)))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(B_371),u1_pre_topc(B_371)))
      | ~ l1_pre_topc(B_371)
      | ~ v2_pre_topc(B_371)
      | ~ l1_pre_topc(A_372)
      | ~ v2_pre_topc(A_372) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_1305,plain,(
    ! [A_372] :
      ( v1_tsep_1('#skF_3',A_372)
      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),A_372)
      | ~ v1_tsep_1(g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3')),A_372)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | ~ l1_pre_topc(A_372)
      | ~ v2_pre_topc(A_372) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_1296])).

tff(c_1316,plain,(
    ! [A_372] :
      ( v1_tsep_1('#skF_3',A_372)
      | ~ m1_pre_topc('#skF_4',A_372)
      | ~ v1_tsep_1('#skF_4',A_372)
      | ~ l1_pre_topc(A_372)
      | ~ v2_pre_topc(A_372) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_170,c_128,c_173,c_140,c_135,c_131,c_140,c_135,c_140,c_140,c_135,c_1305])).

tff(c_720,plain,(
    ! [B_350,A_351] :
      ( v3_pre_topc(u1_struct_0(B_350),A_351)
      | ~ v1_tsep_1(B_350,A_351)
      | ~ m1_subset_1(u1_struct_0(B_350),k1_zfmisc_1(u1_struct_0(A_351)))
      | ~ m1_pre_topc(B_350,A_351)
      | ~ l1_pre_topc(A_351)
      | ~ v2_pre_topc(A_351) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_1706,plain,(
    ! [B_412,A_413] :
      ( v3_pre_topc(u1_struct_0(B_412),A_413)
      | ~ v1_tsep_1(B_412,A_413)
      | ~ v2_pre_topc(A_413)
      | ~ m1_pre_topc(B_412,A_413)
      | ~ l1_pre_topc(A_413) ) ),
    inference(resolution,[status(thm)],[c_32,c_720])).

tff(c_1716,plain,(
    ! [A_413] :
      ( v3_pre_topc(k2_struct_0('#skF_3'),A_413)
      | ~ v1_tsep_1('#skF_3',A_413)
      | ~ v2_pre_topc(A_413)
      | ~ m1_pre_topc('#skF_3',A_413)
      | ~ l1_pre_topc(A_413) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_1706])).

tff(c_448,plain,(
    m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_214])).

tff(c_649,plain,(
    ! [B_348] :
      ( v1_tsep_1(B_348,'#skF_4')
      | ~ v3_pre_topc(u1_struct_0(B_348),'#skF_4')
      | ~ m1_subset_1(u1_struct_0(B_348),k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ m1_pre_topc(B_348,'#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_139,c_640])).

tff(c_2125,plain,(
    ! [B_451] :
      ( v1_tsep_1(B_451,'#skF_4')
      | ~ v3_pre_topc(u1_struct_0(B_451),'#skF_4')
      | ~ m1_subset_1(u1_struct_0(B_451),k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ m1_pre_topc(B_451,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_131,c_649])).

tff(c_2134,plain,
    ( v1_tsep_1('#skF_3','#skF_4')
    | ~ v3_pre_topc(u1_struct_0('#skF_3'),'#skF_4')
    | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_4')))
    | ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_2125])).

tff(c_2145,plain,
    ( v1_tsep_1('#skF_3','#skF_4')
    | ~ v3_pre_topc(k2_struct_0('#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_449,c_448,c_135,c_2134])).

tff(c_2203,plain,(
    ~ v3_pre_topc(k2_struct_0('#skF_3'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_2145])).

tff(c_2206,plain,
    ( ~ v1_tsep_1('#skF_3','#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_1716,c_2203])).

tff(c_2209,plain,(
    ~ v1_tsep_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_449,c_173,c_2206])).

tff(c_2212,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_4')
    | ~ v1_tsep_1('#skF_4','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_1316,c_2209])).

tff(c_2216,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_131,c_1838,c_690,c_2212])).

tff(c_2217,plain,(
    v1_tsep_1('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_2145])).

tff(c_50,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_262])).

tff(c_151,plain,(
    m1_subset_1('#skF_6',k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_50])).

tff(c_46,plain,(
    '#skF_7' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_262])).

tff(c_48,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_262])).

tff(c_79,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_48])).

tff(c_141,plain,(
    m1_subset_1('#skF_6',k2_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_79])).

tff(c_1625,plain,(
    ! [C_401,D_404,B_403,A_402,E_405] :
      ( k3_tmap_1(A_402,B_403,C_401,D_404,E_405) = k2_partfun1(u1_struct_0(C_401),u1_struct_0(B_403),E_405,u1_struct_0(D_404))
      | ~ m1_pre_topc(D_404,C_401)
      | ~ m1_subset_1(E_405,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_401),u1_struct_0(B_403))))
      | ~ v1_funct_2(E_405,u1_struct_0(C_401),u1_struct_0(B_403))
      | ~ v1_funct_1(E_405)
      | ~ m1_pre_topc(D_404,A_402)
      | ~ m1_pre_topc(C_401,A_402)
      | ~ l1_pre_topc(B_403)
      | ~ v2_pre_topc(B_403)
      | v2_struct_0(B_403)
      | ~ l1_pre_topc(A_402)
      | ~ v2_pre_topc(A_402)
      | v2_struct_0(A_402) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_1627,plain,(
    ! [A_402,B_403,D_404,E_405] :
      ( k3_tmap_1(A_402,B_403,'#skF_4',D_404,E_405) = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0(B_403),E_405,u1_struct_0(D_404))
      | ~ m1_pre_topc(D_404,'#skF_4')
      | ~ m1_subset_1(E_405,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'),u1_struct_0(B_403))))
      | ~ v1_funct_2(E_405,u1_struct_0('#skF_4'),u1_struct_0(B_403))
      | ~ v1_funct_1(E_405)
      | ~ m1_pre_topc(D_404,A_402)
      | ~ m1_pre_topc('#skF_4',A_402)
      | ~ l1_pre_topc(B_403)
      | ~ v2_pre_topc(B_403)
      | v2_struct_0(B_403)
      | ~ l1_pre_topc(A_402)
      | ~ v2_pre_topc(A_402)
      | v2_struct_0(A_402) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_139,c_1625])).

tff(c_23413,plain,(
    ! [A_968,B_969,D_970,E_971] :
      ( k3_tmap_1(A_968,B_969,'#skF_4',D_970,E_971) = k2_partfun1(k2_struct_0('#skF_4'),u1_struct_0(B_969),E_971,u1_struct_0(D_970))
      | ~ m1_pre_topc(D_970,'#skF_4')
      | ~ m1_subset_1(E_971,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'),u1_struct_0(B_969))))
      | ~ v1_funct_2(E_971,k2_struct_0('#skF_4'),u1_struct_0(B_969))
      | ~ v1_funct_1(E_971)
      | ~ m1_pre_topc(D_970,A_968)
      | ~ m1_pre_topc('#skF_4',A_968)
      | ~ l1_pre_topc(B_969)
      | ~ v2_pre_topc(B_969)
      | v2_struct_0(B_969)
      | ~ l1_pre_topc(A_968)
      | ~ v2_pre_topc(A_968)
      | v2_struct_0(A_968) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_139,c_1627])).

tff(c_23419,plain,(
    ! [A_968,D_970,E_971] :
      ( k3_tmap_1(A_968,'#skF_2','#skF_4',D_970,E_971) = k2_partfun1(k2_struct_0('#skF_4'),u1_struct_0('#skF_2'),E_971,u1_struct_0(D_970))
      | ~ m1_pre_topc(D_970,'#skF_4')
      | ~ m1_subset_1(E_971,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_971,k2_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_971)
      | ~ m1_pre_topc(D_970,A_968)
      | ~ m1_pre_topc('#skF_4',A_968)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_968)
      | ~ v2_pre_topc(A_968)
      | v2_struct_0(A_968) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_23413])).

tff(c_23429,plain,(
    ! [A_968,D_970,E_971] :
      ( k3_tmap_1(A_968,'#skF_2','#skF_4',D_970,E_971) = k2_partfun1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'),E_971,u1_struct_0(D_970))
      | ~ m1_pre_topc(D_970,'#skF_4')
      | ~ m1_subset_1(E_971,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_971,k2_struct_0('#skF_4'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(E_971)
      | ~ m1_pre_topc(D_970,A_968)
      | ~ m1_pre_topc('#skF_4',A_968)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_968)
      | ~ v2_pre_topc(A_968)
      | v2_struct_0(A_968) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_104,c_104,c_23419])).

tff(c_24286,plain,(
    ! [A_1020,D_1021,E_1022] :
      ( k3_tmap_1(A_1020,'#skF_2','#skF_4',D_1021,E_1022) = k2_partfun1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'),E_1022,u1_struct_0(D_1021))
      | ~ m1_pre_topc(D_1021,'#skF_4')
      | ~ m1_subset_1(E_1022,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_1022,k2_struct_0('#skF_4'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(E_1022)
      | ~ m1_pre_topc(D_1021,A_1020)
      | ~ m1_pre_topc('#skF_4',A_1020)
      | ~ l1_pre_topc(A_1020)
      | ~ v2_pre_topc(A_1020)
      | v2_struct_0(A_1020) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_23429])).

tff(c_24288,plain,(
    ! [A_1020,D_1021] :
      ( k3_tmap_1(A_1020,'#skF_2','#skF_4',D_1021,'#skF_5') = k2_partfun1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_1021))
      | ~ m1_pre_topc(D_1021,'#skF_4')
      | ~ v1_funct_2('#skF_5',k2_struct_0('#skF_4'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_1021,A_1020)
      | ~ m1_pre_topc('#skF_4',A_1020)
      | ~ l1_pre_topc(A_1020)
      | ~ v2_pre_topc(A_1020)
      | v2_struct_0(A_1020) ) ),
    inference(resolution,[status(thm)],[c_174,c_24286])).

tff(c_24292,plain,(
    ! [A_1023,D_1024] :
      ( k3_tmap_1(A_1023,'#skF_2','#skF_4',D_1024,'#skF_5') = k2_partfun1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_1024))
      | ~ m1_pre_topc(D_1024,'#skF_4')
      | ~ m1_pre_topc(D_1024,A_1023)
      | ~ m1_pre_topc('#skF_4',A_1023)
      | ~ l1_pre_topc(A_1023)
      | ~ v2_pre_topc(A_1023)
      | v2_struct_0(A_1023) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_150,c_24288])).

tff(c_24384,plain,
    ( k2_partfun1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_5')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_449,c_24292])).

tff(c_24497,plain,
    ( k2_partfun1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'),'#skF_5',k2_struct_0('#skF_3')) = k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_131,c_690,c_449,c_135,c_24384])).

tff(c_24498,plain,(
    k2_partfun1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'),'#skF_5',k2_struct_0('#skF_3')) = k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_24497])).

tff(c_78,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_262])).

tff(c_24392,plain,
    ( k2_partfun1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_64,c_24292])).

tff(c_24510,plain,
    ( k2_partfun1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'),'#skF_5',k2_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_60,c_449,c_135,c_24392])).

tff(c_24511,plain,(
    k2_partfun1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'),'#skF_5',k2_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_24510])).

tff(c_24603,plain,(
    k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5') = k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24498,c_24511])).

tff(c_44,plain,(
    r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_262])).

tff(c_80,plain,(
    r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44])).

tff(c_24604,plain,(
    r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24603,c_80])).

tff(c_38,plain,(
    ! [B_133,C_165,D_181,E_189,A_69,G_195] :
      ( r1_tmap_1(D_181,A_69,E_189,G_195)
      | ~ r1_tmap_1(C_165,A_69,k3_tmap_1(B_133,A_69,D_181,C_165,E_189),G_195)
      | ~ m1_subset_1(G_195,u1_struct_0(C_165))
      | ~ m1_subset_1(G_195,u1_struct_0(D_181))
      | ~ m1_pre_topc(C_165,D_181)
      | ~ v1_tsep_1(C_165,B_133)
      | ~ m1_subset_1(E_189,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_181),u1_struct_0(A_69))))
      | ~ v1_funct_2(E_189,u1_struct_0(D_181),u1_struct_0(A_69))
      | ~ v1_funct_1(E_189)
      | ~ m1_pre_topc(D_181,B_133)
      | v2_struct_0(D_181)
      | ~ m1_pre_topc(C_165,B_133)
      | v2_struct_0(C_165)
      | ~ l1_pre_topc(B_133)
      | ~ v2_pre_topc(B_133)
      | v2_struct_0(B_133)
      | ~ l1_pre_topc(A_69)
      | ~ v2_pre_topc(A_69)
      | v2_struct_0(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_24650,plain,
    ( r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4'))
    | ~ v1_tsep_1('#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_24604,c_38])).

tff(c_24653,plain,
    ( r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_173,c_131,c_449,c_690,c_58,c_150,c_104,c_139,c_174,c_104,c_139,c_2217,c_151,c_139,c_141,c_135,c_24650])).

tff(c_24655,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_62,c_66,c_42,c_24653])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n005.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 20:36:47 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 14.01/7.03  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.01/7.05  
% 14.01/7.05  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.01/7.05  %$ r1_tmap_1 > v1_funct_2 > v3_pre_topc > v1_tsep_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k2_partfun1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 14.01/7.05  
% 14.01/7.05  %Foreground sorts:
% 14.01/7.05  
% 14.01/7.05  
% 14.01/7.05  %Background operators:
% 14.01/7.05  
% 14.01/7.05  
% 14.01/7.05  %Foreground operators:
% 14.01/7.05  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 14.01/7.05  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 14.01/7.05  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 14.01/7.05  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 14.01/7.05  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 14.01/7.05  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 14.01/7.05  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 14.01/7.05  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 14.01/7.05  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 14.01/7.05  tff('#skF_7', type, '#skF_7': $i).
% 14.01/7.05  tff('#skF_5', type, '#skF_5': $i).
% 14.01/7.05  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 14.01/7.05  tff('#skF_6', type, '#skF_6': $i).
% 14.01/7.05  tff('#skF_2', type, '#skF_2': $i).
% 14.01/7.05  tff('#skF_3', type, '#skF_3': $i).
% 14.01/7.05  tff('#skF_1', type, '#skF_1': $i).
% 14.01/7.05  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 14.01/7.05  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 14.01/7.05  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 14.01/7.05  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 14.01/7.05  tff(v1_tsep_1, type, v1_tsep_1: ($i * $i) > $o).
% 14.01/7.05  tff('#skF_4', type, '#skF_4': $i).
% 14.01/7.05  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 14.01/7.05  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 14.01/7.05  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 14.01/7.05  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 14.01/7.05  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 14.01/7.05  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 14.01/7.05  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 14.01/7.05  
% 14.01/7.07  tff(f_262, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((g1_pre_topc(u1_struct_0(C), u1_pre_topc(C)) = D) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => (((F = G) & r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), G)) => r1_tmap_1(D, B, E, F))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_tmap_1)).
% 14.01/7.07  tff(f_34, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_pre_topc)).
% 14.01/7.07  tff(f_49, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 14.01/7.07  tff(f_42, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 14.01/7.07  tff(f_38, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 14.01/7.07  tff(f_145, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 14.01/7.07  tff(f_149, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tsep_1)).
% 14.01/7.07  tff(f_58, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (m1_pre_topc(A, B) <=> m1_pre_topc(A, g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_pre_topc)).
% 14.01/7.07  tff(f_64, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v3_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc10_tops_1)).
% 14.01/7.07  tff(f_138, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => ((v1_tsep_1(B, A) & m1_pre_topc(B, A)) <=> v3_pre_topc(C, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_tsep_1)).
% 14.01/7.07  tff(f_120, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: ((v2_pre_topc(B) & l1_pre_topc(B)) => (![C]: ((v2_pre_topc(C) & l1_pre_topc(C)) => ((C = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) => ((v1_tsep_1(B, A) & m1_pre_topc(B, A)) <=> (v1_tsep_1(C, A) & m1_pre_topc(C, A)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_tmap_1)).
% 14.01/7.07  tff(f_96, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (m1_pre_topc(C, A) => (![D]: (m1_pre_topc(D, A) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (m1_pre_topc(D, C) => (k3_tmap_1(A, B, C, D, E) = k2_partfun1(u1_struct_0(C), u1_struct_0(B), E, u1_struct_0(D)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tmap_1)).
% 14.01/7.07  tff(f_213, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, B)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(A))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(A))))) => (((v1_tsep_1(C, B) & m1_pre_topc(C, B)) & m1_pre_topc(C, D)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => ((F = G) => (r1_tmap_1(D, A, E, F) <=> r1_tmap_1(C, A, k3_tmap_1(B, A, D, C, E), G)))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_tmap_1)).
% 14.01/7.07  tff(c_72, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_262])).
% 14.01/7.07  tff(c_62, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_262])).
% 14.01/7.07  tff(c_66, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_262])).
% 14.01/7.07  tff(c_42, plain, (~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_262])).
% 14.01/7.07  tff(c_70, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_262])).
% 14.01/7.07  tff(c_68, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_262])).
% 14.01/7.07  tff(c_76, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_262])).
% 14.01/7.07  tff(c_74, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_262])).
% 14.01/7.07  tff(c_60, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_262])).
% 14.01/7.07  tff(c_157, plain, (![B_323, A_324]: (v2_pre_topc(B_323) | ~m1_pre_topc(B_323, A_324) | ~l1_pre_topc(A_324) | ~v2_pre_topc(A_324))), inference(cnfTransformation, [status(thm)], [f_34])).
% 14.01/7.07  tff(c_166, plain, (v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_60, c_157])).
% 14.01/7.07  tff(c_173, plain, (v2_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_166])).
% 14.01/7.07  tff(c_115, plain, (![B_320, A_321]: (l1_pre_topc(B_320) | ~m1_pre_topc(B_320, A_321) | ~l1_pre_topc(A_321))), inference(cnfTransformation, [status(thm)], [f_49])).
% 14.01/7.07  tff(c_124, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_60, c_115])).
% 14.01/7.07  tff(c_131, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_124])).
% 14.01/7.07  tff(c_64, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_262])).
% 14.01/7.07  tff(c_121, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_64, c_115])).
% 14.01/7.07  tff(c_128, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_121])).
% 14.01/7.07  tff(c_6, plain, (![A_5]: (l1_struct_0(A_5) | ~l1_pre_topc(A_5))), inference(cnfTransformation, [status(thm)], [f_42])).
% 14.01/7.07  tff(c_91, plain, (![A_318]: (u1_struct_0(A_318)=k2_struct_0(A_318) | ~l1_struct_0(A_318))), inference(cnfTransformation, [status(thm)], [f_38])).
% 14.01/7.07  tff(c_95, plain, (![A_5]: (u1_struct_0(A_5)=k2_struct_0(A_5) | ~l1_pre_topc(A_5))), inference(resolution, [status(thm)], [c_6, c_91])).
% 14.01/7.07  tff(c_135, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_128, c_95])).
% 14.01/7.07  tff(c_139, plain, (u1_struct_0('#skF_4')=k2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_131, c_95])).
% 14.01/7.07  tff(c_175, plain, (![B_325, A_326]: (m1_subset_1(u1_struct_0(B_325), k1_zfmisc_1(u1_struct_0(A_326))) | ~m1_pre_topc(B_325, A_326) | ~l1_pre_topc(A_326))), inference(cnfTransformation, [status(thm)], [f_145])).
% 14.01/7.07  tff(c_181, plain, (![B_325]: (m1_subset_1(u1_struct_0(B_325), k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~m1_pre_topc(B_325, '#skF_4') | ~l1_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_139, c_175])).
% 14.01/7.07  tff(c_208, plain, (![B_327]: (m1_subset_1(u1_struct_0(B_327), k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~m1_pre_topc(B_327, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_131, c_181])).
% 14.01/7.07  tff(c_214, plain, (m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~m1_pre_topc('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_135, c_208])).
% 14.01/7.07  tff(c_370, plain, (~m1_pre_topc('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_214])).
% 14.01/7.07  tff(c_34, plain, (![A_61]: (m1_pre_topc(A_61, A_61) | ~l1_pre_topc(A_61))), inference(cnfTransformation, [status(thm)], [f_149])).
% 14.01/7.07  tff(c_187, plain, (![B_325]: (m1_subset_1(u1_struct_0(B_325), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_pre_topc(B_325, '#skF_3') | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_135, c_175])).
% 14.01/7.07  tff(c_221, plain, (![B_328]: (m1_subset_1(u1_struct_0(B_328), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_pre_topc(B_328, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_128, c_187])).
% 14.01/7.07  tff(c_227, plain, (m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_pre_topc('#skF_3', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_135, c_221])).
% 14.01/7.07  tff(c_274, plain, (~m1_pre_topc('#skF_3', '#skF_3')), inference(splitLeft, [status(thm)], [c_227])).
% 14.01/7.07  tff(c_294, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_34, c_274])).
% 14.01/7.07  tff(c_301, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_128, c_294])).
% 14.01/7.07  tff(c_303, plain, (m1_pre_topc('#skF_3', '#skF_3')), inference(splitRight, [status(thm)], [c_227])).
% 14.01/7.07  tff(c_52, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))='#skF_4'), inference(cnfTransformation, [status(thm)], [f_262])).
% 14.01/7.07  tff(c_140, plain, (g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_135, c_52])).
% 14.01/7.07  tff(c_388, plain, (![A_340, B_341]: (m1_pre_topc(A_340, g1_pre_topc(u1_struct_0(B_341), u1_pre_topc(B_341))) | ~m1_pre_topc(A_340, B_341) | ~l1_pre_topc(B_341) | ~l1_pre_topc(A_340))), inference(cnfTransformation, [status(thm)], [f_58])).
% 14.01/7.07  tff(c_409, plain, (![A_340]: (m1_pre_topc(A_340, g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~m1_pre_topc(A_340, '#skF_3') | ~l1_pre_topc('#skF_3') | ~l1_pre_topc(A_340))), inference(superposition, [status(thm), theory('equality')], [c_135, c_388])).
% 14.01/7.07  tff(c_431, plain, (![A_342]: (m1_pre_topc(A_342, '#skF_4') | ~m1_pre_topc(A_342, '#skF_3') | ~l1_pre_topc(A_342))), inference(demodulation, [status(thm), theory('equality')], [c_128, c_140, c_409])).
% 14.01/7.07  tff(c_437, plain, (m1_pre_topc('#skF_3', '#skF_4') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_303, c_431])).
% 14.01/7.07  tff(c_445, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_128, c_437])).
% 14.01/7.07  tff(c_447, plain, $false, inference(negUnitSimplification, [status(thm)], [c_370, c_445])).
% 14.01/7.07  tff(c_449, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_214])).
% 14.01/7.07  tff(c_211, plain, (m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~m1_pre_topc('#skF_4', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_139, c_208])).
% 14.01/7.07  tff(c_681, plain, (~m1_pre_topc('#skF_4', '#skF_4')), inference(splitLeft, [status(thm)], [c_211])).
% 14.01/7.07  tff(c_684, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_34, c_681])).
% 14.01/7.07  tff(c_688, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_131, c_684])).
% 14.01/7.07  tff(c_690, plain, (m1_pre_topc('#skF_4', '#skF_4')), inference(splitRight, [status(thm)], [c_211])).
% 14.01/7.07  tff(c_58, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_262])).
% 14.01/7.07  tff(c_96, plain, (![A_319]: (u1_struct_0(A_319)=k2_struct_0(A_319) | ~l1_pre_topc(A_319))), inference(resolution, [status(thm)], [c_6, c_91])).
% 14.01/7.07  tff(c_104, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_68, c_96])).
% 14.01/7.07  tff(c_56, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_262])).
% 14.01/7.07  tff(c_110, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_56])).
% 14.01/7.07  tff(c_150, plain, (v1_funct_2('#skF_5', k2_struct_0('#skF_4'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_139, c_110])).
% 14.01/7.07  tff(c_54, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_262])).
% 14.01/7.07  tff(c_109, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_54])).
% 14.01/7.07  tff(c_174, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_139, c_109])).
% 14.01/7.07  tff(c_14, plain, (![A_12]: (v3_pre_topc(k2_struct_0(A_12), A_12) | ~l1_pre_topc(A_12) | ~v2_pre_topc(A_12))), inference(cnfTransformation, [status(thm)], [f_64])).
% 14.01/7.07  tff(c_32, plain, (![B_60, A_58]: (m1_subset_1(u1_struct_0(B_60), k1_zfmisc_1(u1_struct_0(A_58))) | ~m1_pre_topc(B_60, A_58) | ~l1_pre_topc(A_58))), inference(cnfTransformation, [status(thm)], [f_145])).
% 14.01/7.07  tff(c_640, plain, (![B_348, A_349]: (v1_tsep_1(B_348, A_349) | ~v3_pre_topc(u1_struct_0(B_348), A_349) | ~m1_subset_1(u1_struct_0(B_348), k1_zfmisc_1(u1_struct_0(A_349))) | ~m1_pre_topc(B_348, A_349) | ~l1_pre_topc(A_349) | ~v2_pre_topc(A_349))), inference(cnfTransformation, [status(thm)], [f_138])).
% 14.01/7.07  tff(c_1726, plain, (![B_414, A_415]: (v1_tsep_1(B_414, A_415) | ~v3_pre_topc(u1_struct_0(B_414), A_415) | ~v2_pre_topc(A_415) | ~m1_pre_topc(B_414, A_415) | ~l1_pre_topc(A_415))), inference(resolution, [status(thm)], [c_32, c_640])).
% 14.01/7.07  tff(c_1827, plain, (![A_433]: (v1_tsep_1('#skF_4', A_433) | ~v3_pre_topc(k2_struct_0('#skF_4'), A_433) | ~v2_pre_topc(A_433) | ~m1_pre_topc('#skF_4', A_433) | ~l1_pre_topc(A_433))), inference(superposition, [status(thm), theory('equality')], [c_139, c_1726])).
% 14.01/7.07  tff(c_1834, plain, (v1_tsep_1('#skF_4', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_14, c_1827])).
% 14.01/7.07  tff(c_1838, plain, (v1_tsep_1('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_173, c_131, c_690, c_1834])).
% 14.01/7.07  tff(c_163, plain, (v2_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_64, c_157])).
% 14.01/7.07  tff(c_170, plain, (v2_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_163])).
% 14.01/7.07  tff(c_1296, plain, (![B_371, A_372]: (v1_tsep_1(B_371, A_372) | ~m1_pre_topc(g1_pre_topc(u1_struct_0(B_371), u1_pre_topc(B_371)), A_372) | ~v1_tsep_1(g1_pre_topc(u1_struct_0(B_371), u1_pre_topc(B_371)), A_372) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(B_371), u1_pre_topc(B_371))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(B_371), u1_pre_topc(B_371))) | ~l1_pre_topc(B_371) | ~v2_pre_topc(B_371) | ~l1_pre_topc(A_372) | ~v2_pre_topc(A_372))), inference(cnfTransformation, [status(thm)], [f_120])).
% 14.01/7.07  tff(c_1305, plain, (![A_372]: (v1_tsep_1('#skF_3', A_372) | ~m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')), A_372) | ~v1_tsep_1(g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3')), A_372) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | ~l1_pre_topc(A_372) | ~v2_pre_topc(A_372))), inference(superposition, [status(thm), theory('equality')], [c_135, c_1296])).
% 14.01/7.07  tff(c_1316, plain, (![A_372]: (v1_tsep_1('#skF_3', A_372) | ~m1_pre_topc('#skF_4', A_372) | ~v1_tsep_1('#skF_4', A_372) | ~l1_pre_topc(A_372) | ~v2_pre_topc(A_372))), inference(demodulation, [status(thm), theory('equality')], [c_170, c_128, c_173, c_140, c_135, c_131, c_140, c_135, c_140, c_140, c_135, c_1305])).
% 14.01/7.07  tff(c_720, plain, (![B_350, A_351]: (v3_pre_topc(u1_struct_0(B_350), A_351) | ~v1_tsep_1(B_350, A_351) | ~m1_subset_1(u1_struct_0(B_350), k1_zfmisc_1(u1_struct_0(A_351))) | ~m1_pre_topc(B_350, A_351) | ~l1_pre_topc(A_351) | ~v2_pre_topc(A_351))), inference(cnfTransformation, [status(thm)], [f_138])).
% 14.01/7.07  tff(c_1706, plain, (![B_412, A_413]: (v3_pre_topc(u1_struct_0(B_412), A_413) | ~v1_tsep_1(B_412, A_413) | ~v2_pre_topc(A_413) | ~m1_pre_topc(B_412, A_413) | ~l1_pre_topc(A_413))), inference(resolution, [status(thm)], [c_32, c_720])).
% 14.01/7.07  tff(c_1716, plain, (![A_413]: (v3_pre_topc(k2_struct_0('#skF_3'), A_413) | ~v1_tsep_1('#skF_3', A_413) | ~v2_pre_topc(A_413) | ~m1_pre_topc('#skF_3', A_413) | ~l1_pre_topc(A_413))), inference(superposition, [status(thm), theory('equality')], [c_135, c_1706])).
% 14.01/7.07  tff(c_448, plain, (m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_4')))), inference(splitRight, [status(thm)], [c_214])).
% 14.01/7.07  tff(c_649, plain, (![B_348]: (v1_tsep_1(B_348, '#skF_4') | ~v3_pre_topc(u1_struct_0(B_348), '#skF_4') | ~m1_subset_1(u1_struct_0(B_348), k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~m1_pre_topc(B_348, '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_139, c_640])).
% 14.01/7.07  tff(c_2125, plain, (![B_451]: (v1_tsep_1(B_451, '#skF_4') | ~v3_pre_topc(u1_struct_0(B_451), '#skF_4') | ~m1_subset_1(u1_struct_0(B_451), k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~m1_pre_topc(B_451, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_173, c_131, c_649])).
% 14.01/7.07  tff(c_2134, plain, (v1_tsep_1('#skF_3', '#skF_4') | ~v3_pre_topc(u1_struct_0('#skF_3'), '#skF_4') | ~m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~m1_pre_topc('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_135, c_2125])).
% 14.01/7.07  tff(c_2145, plain, (v1_tsep_1('#skF_3', '#skF_4') | ~v3_pre_topc(k2_struct_0('#skF_3'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_449, c_448, c_135, c_2134])).
% 14.01/7.07  tff(c_2203, plain, (~v3_pre_topc(k2_struct_0('#skF_3'), '#skF_4')), inference(splitLeft, [status(thm)], [c_2145])).
% 14.01/7.07  tff(c_2206, plain, (~v1_tsep_1('#skF_3', '#skF_4') | ~v2_pre_topc('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_1716, c_2203])).
% 14.01/7.07  tff(c_2209, plain, (~v1_tsep_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_131, c_449, c_173, c_2206])).
% 14.01/7.07  tff(c_2212, plain, (~m1_pre_topc('#skF_4', '#skF_4') | ~v1_tsep_1('#skF_4', '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_1316, c_2209])).
% 14.01/7.07  tff(c_2216, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_173, c_131, c_1838, c_690, c_2212])).
% 14.01/7.07  tff(c_2217, plain, (v1_tsep_1('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_2145])).
% 14.01/7.07  tff(c_50, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_262])).
% 14.01/7.07  tff(c_151, plain, (m1_subset_1('#skF_6', k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_139, c_50])).
% 14.01/7.07  tff(c_46, plain, ('#skF_7'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_262])).
% 14.01/7.07  tff(c_48, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_262])).
% 14.01/7.07  tff(c_79, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_48])).
% 14.01/7.07  tff(c_141, plain, (m1_subset_1('#skF_6', k2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_135, c_79])).
% 14.01/7.07  tff(c_1625, plain, (![C_401, D_404, B_403, A_402, E_405]: (k3_tmap_1(A_402, B_403, C_401, D_404, E_405)=k2_partfun1(u1_struct_0(C_401), u1_struct_0(B_403), E_405, u1_struct_0(D_404)) | ~m1_pre_topc(D_404, C_401) | ~m1_subset_1(E_405, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_401), u1_struct_0(B_403)))) | ~v1_funct_2(E_405, u1_struct_0(C_401), u1_struct_0(B_403)) | ~v1_funct_1(E_405) | ~m1_pre_topc(D_404, A_402) | ~m1_pre_topc(C_401, A_402) | ~l1_pre_topc(B_403) | ~v2_pre_topc(B_403) | v2_struct_0(B_403) | ~l1_pre_topc(A_402) | ~v2_pre_topc(A_402) | v2_struct_0(A_402))), inference(cnfTransformation, [status(thm)], [f_96])).
% 14.01/7.07  tff(c_1627, plain, (![A_402, B_403, D_404, E_405]: (k3_tmap_1(A_402, B_403, '#skF_4', D_404, E_405)=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0(B_403), E_405, u1_struct_0(D_404)) | ~m1_pre_topc(D_404, '#skF_4') | ~m1_subset_1(E_405, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), u1_struct_0(B_403)))) | ~v1_funct_2(E_405, u1_struct_0('#skF_4'), u1_struct_0(B_403)) | ~v1_funct_1(E_405) | ~m1_pre_topc(D_404, A_402) | ~m1_pre_topc('#skF_4', A_402) | ~l1_pre_topc(B_403) | ~v2_pre_topc(B_403) | v2_struct_0(B_403) | ~l1_pre_topc(A_402) | ~v2_pre_topc(A_402) | v2_struct_0(A_402))), inference(superposition, [status(thm), theory('equality')], [c_139, c_1625])).
% 14.01/7.07  tff(c_23413, plain, (![A_968, B_969, D_970, E_971]: (k3_tmap_1(A_968, B_969, '#skF_4', D_970, E_971)=k2_partfun1(k2_struct_0('#skF_4'), u1_struct_0(B_969), E_971, u1_struct_0(D_970)) | ~m1_pre_topc(D_970, '#skF_4') | ~m1_subset_1(E_971, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), u1_struct_0(B_969)))) | ~v1_funct_2(E_971, k2_struct_0('#skF_4'), u1_struct_0(B_969)) | ~v1_funct_1(E_971) | ~m1_pre_topc(D_970, A_968) | ~m1_pre_topc('#skF_4', A_968) | ~l1_pre_topc(B_969) | ~v2_pre_topc(B_969) | v2_struct_0(B_969) | ~l1_pre_topc(A_968) | ~v2_pre_topc(A_968) | v2_struct_0(A_968))), inference(demodulation, [status(thm), theory('equality')], [c_139, c_139, c_1627])).
% 14.01/7.07  tff(c_23419, plain, (![A_968, D_970, E_971]: (k3_tmap_1(A_968, '#skF_2', '#skF_4', D_970, E_971)=k2_partfun1(k2_struct_0('#skF_4'), u1_struct_0('#skF_2'), E_971, u1_struct_0(D_970)) | ~m1_pre_topc(D_970, '#skF_4') | ~m1_subset_1(E_971, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2')))) | ~v1_funct_2(E_971, k2_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(E_971) | ~m1_pre_topc(D_970, A_968) | ~m1_pre_topc('#skF_4', A_968) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_968) | ~v2_pre_topc(A_968) | v2_struct_0(A_968))), inference(superposition, [status(thm), theory('equality')], [c_104, c_23413])).
% 14.01/7.07  tff(c_23429, plain, (![A_968, D_970, E_971]: (k3_tmap_1(A_968, '#skF_2', '#skF_4', D_970, E_971)=k2_partfun1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'), E_971, u1_struct_0(D_970)) | ~m1_pre_topc(D_970, '#skF_4') | ~m1_subset_1(E_971, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2')))) | ~v1_funct_2(E_971, k2_struct_0('#skF_4'), k2_struct_0('#skF_2')) | ~v1_funct_1(E_971) | ~m1_pre_topc(D_970, A_968) | ~m1_pre_topc('#skF_4', A_968) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_968) | ~v2_pre_topc(A_968) | v2_struct_0(A_968))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_104, c_104, c_23419])).
% 14.01/7.07  tff(c_24286, plain, (![A_1020, D_1021, E_1022]: (k3_tmap_1(A_1020, '#skF_2', '#skF_4', D_1021, E_1022)=k2_partfun1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'), E_1022, u1_struct_0(D_1021)) | ~m1_pre_topc(D_1021, '#skF_4') | ~m1_subset_1(E_1022, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2')))) | ~v1_funct_2(E_1022, k2_struct_0('#skF_4'), k2_struct_0('#skF_2')) | ~v1_funct_1(E_1022) | ~m1_pre_topc(D_1021, A_1020) | ~m1_pre_topc('#skF_4', A_1020) | ~l1_pre_topc(A_1020) | ~v2_pre_topc(A_1020) | v2_struct_0(A_1020))), inference(negUnitSimplification, [status(thm)], [c_72, c_23429])).
% 14.01/7.07  tff(c_24288, plain, (![A_1020, D_1021]: (k3_tmap_1(A_1020, '#skF_2', '#skF_4', D_1021, '#skF_5')=k2_partfun1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_1021)) | ~m1_pre_topc(D_1021, '#skF_4') | ~v1_funct_2('#skF_5', k2_struct_0('#skF_4'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_1021, A_1020) | ~m1_pre_topc('#skF_4', A_1020) | ~l1_pre_topc(A_1020) | ~v2_pre_topc(A_1020) | v2_struct_0(A_1020))), inference(resolution, [status(thm)], [c_174, c_24286])).
% 14.01/7.07  tff(c_24292, plain, (![A_1023, D_1024]: (k3_tmap_1(A_1023, '#skF_2', '#skF_4', D_1024, '#skF_5')=k2_partfun1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_1024)) | ~m1_pre_topc(D_1024, '#skF_4') | ~m1_pre_topc(D_1024, A_1023) | ~m1_pre_topc('#skF_4', A_1023) | ~l1_pre_topc(A_1023) | ~v2_pre_topc(A_1023) | v2_struct_0(A_1023))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_150, c_24288])).
% 14.01/7.07  tff(c_24384, plain, (k2_partfun1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_5') | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_449, c_24292])).
% 14.01/7.07  tff(c_24497, plain, (k2_partfun1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'), '#skF_5', k2_struct_0('#skF_3'))=k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_173, c_131, c_690, c_449, c_135, c_24384])).
% 14.01/7.07  tff(c_24498, plain, (k2_partfun1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'), '#skF_5', k2_struct_0('#skF_3'))=k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_62, c_24497])).
% 14.01/7.07  tff(c_78, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_262])).
% 14.01/7.07  tff(c_24392, plain, (k2_partfun1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5') | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_64, c_24292])).
% 14.01/7.07  tff(c_24510, plain, (k2_partfun1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'), '#skF_5', k2_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_60, c_449, c_135, c_24392])).
% 14.01/7.07  tff(c_24511, plain, (k2_partfun1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'), '#skF_5', k2_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_78, c_24510])).
% 14.01/7.07  tff(c_24603, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5')=k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_24498, c_24511])).
% 14.01/7.07  tff(c_44, plain, (r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_262])).
% 14.01/7.07  tff(c_80, plain, (r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44])).
% 14.01/7.07  tff(c_24604, plain, (r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_24603, c_80])).
% 14.01/7.07  tff(c_38, plain, (![B_133, C_165, D_181, E_189, A_69, G_195]: (r1_tmap_1(D_181, A_69, E_189, G_195) | ~r1_tmap_1(C_165, A_69, k3_tmap_1(B_133, A_69, D_181, C_165, E_189), G_195) | ~m1_subset_1(G_195, u1_struct_0(C_165)) | ~m1_subset_1(G_195, u1_struct_0(D_181)) | ~m1_pre_topc(C_165, D_181) | ~v1_tsep_1(C_165, B_133) | ~m1_subset_1(E_189, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_181), u1_struct_0(A_69)))) | ~v1_funct_2(E_189, u1_struct_0(D_181), u1_struct_0(A_69)) | ~v1_funct_1(E_189) | ~m1_pre_topc(D_181, B_133) | v2_struct_0(D_181) | ~m1_pre_topc(C_165, B_133) | v2_struct_0(C_165) | ~l1_pre_topc(B_133) | ~v2_pre_topc(B_133) | v2_struct_0(B_133) | ~l1_pre_topc(A_69) | ~v2_pre_topc(A_69) | v2_struct_0(A_69))), inference(cnfTransformation, [status(thm)], [f_213])).
% 14.01/7.07  tff(c_24650, plain, (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4')) | ~v1_tsep_1('#skF_3', '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_4') | ~m1_pre_topc('#skF_3', '#skF_4') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_24604, c_38])).
% 14.01/7.07  tff(c_24653, plain, (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6') | v2_struct_0('#skF_3') | v2_struct_0('#skF_4') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_173, c_131, c_449, c_690, c_58, c_150, c_104, c_139, c_174, c_104, c_139, c_2217, c_151, c_139, c_141, c_135, c_24650])).
% 14.01/7.07  tff(c_24655, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_62, c_66, c_42, c_24653])).
% 14.01/7.07  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.01/7.07  
% 14.01/7.07  Inference rules
% 14.01/7.07  ----------------------
% 14.01/7.07  #Ref     : 0
% 14.01/7.07  #Sup     : 5451
% 14.01/7.07  #Fact    : 0
% 14.01/7.07  #Define  : 0
% 14.01/7.07  #Split   : 29
% 14.01/7.07  #Chain   : 0
% 14.01/7.07  #Close   : 0
% 14.01/7.07  
% 14.01/7.07  Ordering : KBO
% 14.01/7.07  
% 14.01/7.07  Simplification rules
% 14.01/7.07  ----------------------
% 14.01/7.07  #Subsume      : 3394
% 14.01/7.07  #Demod        : 10555
% 14.01/7.07  #Tautology    : 793
% 14.01/7.07  #SimpNegUnit  : 200
% 14.01/7.07  #BackRed      : 8
% 14.01/7.07  
% 14.01/7.07  #Partial instantiations: 0
% 14.01/7.07  #Strategies tried      : 1
% 14.01/7.07  
% 14.01/7.07  Timing (in seconds)
% 14.01/7.07  ----------------------
% 14.01/7.08  Preprocessing        : 0.45
% 14.01/7.08  Parsing              : 0.23
% 14.01/7.08  CNF conversion       : 0.06
% 14.01/7.08  Main loop            : 5.81
% 14.01/7.08  Inferencing          : 0.88
% 14.01/7.08  Reduction            : 1.89
% 14.01/7.08  Demodulation         : 1.46
% 14.01/7.08  BG Simplification    : 0.08
% 14.01/7.08  Subsumption          : 2.78
% 14.01/7.08  Abstraction          : 0.19
% 14.01/7.08  MUC search           : 0.00
% 14.01/7.08  Cooper               : 0.00
% 14.01/7.08  Total                : 6.31
% 14.01/7.08  Index Insertion      : 0.00
% 14.01/7.08  Index Deletion       : 0.00
% 14.01/7.08  Index Matching       : 0.00
% 14.01/7.08  BG Taut test         : 0.00
%------------------------------------------------------------------------------
