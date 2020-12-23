%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:48 EST 2020

% Result     : Theorem 4.75s
% Output     : CNFRefutation 5.15s
% Verified   : 
% Statistics : Number of formulae       :  166 (4131 expanded)
%              Number of leaves         :   39 (1647 expanded)
%              Depth                    :   33
%              Number of atoms          :  722 (30114 expanded)
%              Number of equality atoms :   42 (1800 expanded)
%              Maximal formula depth    :   26 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_funct_2 > v1_funct_2 > r2_hidden > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k3_funct_2 > k4_tmap_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k3_tmap_1,type,(
    k3_tmap_1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k4_tmap_1,type,(
    k4_tmap_1: ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

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

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

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

tff(f_288,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & m1_pre_topc(B,A) )
           => ! [C] :
                ( ( v1_funct_1(C)
                  & v1_funct_2(C,u1_struct_0(B),u1_struct_0(A))
                  & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B),u1_struct_0(A)))) )
               => ( ! [D] :
                      ( m1_subset_1(D,u1_struct_0(A))
                     => ( r2_hidden(D,u1_struct_0(B))
                       => D = k1_funct_1(C,D) ) )
                 => r2_funct_2(u1_struct_0(B),u1_struct_0(A),k4_tmap_1(A,B),C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t96_tmap_1)).

tff(f_71,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_64,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_31,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_79,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_140,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_pre_topc(B,A) )
     => ( v1_funct_1(k4_tmap_1(A,B))
        & v1_funct_2(k4_tmap_1(A,B),u1_struct_0(B),u1_struct_0(A))
        & m1_subset_1(k4_tmap_1(A,B),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B),u1_struct_0(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_tmap_1)).

tff(f_60,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_funct_2(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_funct_2)).

tff(f_144,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_196,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_tmap_1)).

tff(f_125,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_tmap_1)).

tff(f_226,axiom,(
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
                & m1_pre_topc(C,A) )
             => ! [D] :
                  ( ( v1_funct_1(D)
                    & v1_funct_2(D,u1_struct_0(C),u1_struct_0(B))
                    & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(B)))) )
                 => r2_funct_2(u1_struct_0(C),u1_struct_0(B),D,k3_tmap_1(A,B,C,C,D)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tmap_1)).

tff(f_95,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(B))
             => m1_subset_1(C,u1_struct_0(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_pre_topc)).

tff(f_44,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => k3_funct_2(A,B,C,D) = k1_funct_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

tff(f_258,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r2_hidden(C,u1_struct_0(B))
               => k1_funct_1(k4_tmap_1(A,B),C) = C ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_tmap_1)).

tff(c_58,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_288])).

tff(c_54,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_288])).

tff(c_65,plain,(
    ! [B_200,A_201] :
      ( l1_pre_topc(B_200)
      | ~ m1_pre_topc(B_200,A_201)
      | ~ l1_pre_topc(A_201) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_71,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_65])).

tff(c_75,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_71])).

tff(c_10,plain,(
    ! [A_11] :
      ( l1_struct_0(A_11)
      | ~ l1_pre_topc(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_288])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r2_hidden(A_1,B_2)
      | v1_xboole_0(B_2)
      | ~ m1_subset_1(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_78,plain,(
    ! [D_205] :
      ( k1_funct_1('#skF_4',D_205) = D_205
      | ~ r2_hidden(D_205,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(D_205,u1_struct_0('#skF_2')) ) ),
    inference(cnfTransformation,[status(thm)],[f_288])).

tff(c_83,plain,(
    ! [A_1] :
      ( k1_funct_1('#skF_4',A_1) = A_1
      | ~ m1_subset_1(A_1,u1_struct_0('#skF_2'))
      | v1_xboole_0(u1_struct_0('#skF_3'))
      | ~ m1_subset_1(A_1,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_2,c_78])).

tff(c_100,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_83])).

tff(c_14,plain,(
    ! [A_15] :
      ( ~ v1_xboole_0(u1_struct_0(A_15))
      | ~ l1_struct_0(A_15)
      | v2_struct_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_103,plain,
    ( ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_100,c_14])).

tff(c_106,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_103])).

tff(c_109,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_10,c_106])).

tff(c_113,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_109])).

tff(c_115,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_83])).

tff(c_62,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_288])).

tff(c_60,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_288])).

tff(c_24,plain,(
    ! [A_28,B_29] :
      ( m1_subset_1(k4_tmap_1(A_28,B_29),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_29),u1_struct_0(A_28))))
      | ~ m1_pre_topc(B_29,A_28)
      | ~ l1_pre_topc(A_28)
      | ~ v2_pre_topc(A_28)
      | v2_struct_0(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_52,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_288])).

tff(c_50,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_288])).

tff(c_48,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_288])).

tff(c_119,plain,(
    ! [A_218,B_219,D_220] :
      ( r2_funct_2(A_218,B_219,D_220,D_220)
      | ~ m1_subset_1(D_220,k1_zfmisc_1(k2_zfmisc_1(A_218,B_219)))
      | ~ v1_funct_2(D_220,A_218,B_219)
      | ~ v1_funct_1(D_220) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_121,plain,
    ( r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4','#skF_4')
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_119])).

tff(c_124,plain,(
    r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_121])).

tff(c_28,plain,(
    ! [A_28,B_29] :
      ( v1_funct_1(k4_tmap_1(A_28,B_29))
      | ~ m1_pre_topc(B_29,A_28)
      | ~ l1_pre_topc(A_28)
      | ~ v2_pre_topc(A_28)
      | v2_struct_0(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_30,plain,(
    ! [A_30] :
      ( m1_pre_topc(A_30,A_30)
      | ~ l1_pre_topc(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_286,plain,(
    ! [A_288,E_286,C_289,B_290,D_287,F_291] :
      ( r2_hidden('#skF_1'(E_286,D_287,A_288,C_289,B_290,F_291),u1_struct_0(C_289))
      | r2_funct_2(u1_struct_0(C_289),u1_struct_0(B_290),k3_tmap_1(A_288,B_290,D_287,C_289,E_286),F_291)
      | ~ m1_subset_1(F_291,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_289),u1_struct_0(B_290))))
      | ~ v1_funct_2(F_291,u1_struct_0(C_289),u1_struct_0(B_290))
      | ~ v1_funct_1(F_291)
      | ~ m1_pre_topc(C_289,D_287)
      | ~ m1_subset_1(E_286,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_287),u1_struct_0(B_290))))
      | ~ v1_funct_2(E_286,u1_struct_0(D_287),u1_struct_0(B_290))
      | ~ v1_funct_1(E_286)
      | ~ m1_pre_topc(D_287,A_288)
      | v2_struct_0(D_287)
      | ~ m1_pre_topc(C_289,A_288)
      | v2_struct_0(C_289)
      | ~ l1_pre_topc(B_290)
      | ~ v2_pre_topc(B_290)
      | v2_struct_0(B_290)
      | ~ l1_pre_topc(A_288)
      | ~ v2_pre_topc(A_288)
      | v2_struct_0(A_288) ) ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_292,plain,(
    ! [E_286,D_287,A_288] :
      ( r2_hidden('#skF_1'(E_286,D_287,A_288,'#skF_3','#skF_2','#skF_4'),u1_struct_0('#skF_3'))
      | r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1(A_288,'#skF_2',D_287,'#skF_3',E_286),'#skF_4')
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_4')
      | ~ m1_pre_topc('#skF_3',D_287)
      | ~ m1_subset_1(E_286,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_287),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_286,u1_struct_0(D_287),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_286)
      | ~ m1_pre_topc(D_287,A_288)
      | v2_struct_0(D_287)
      | ~ m1_pre_topc('#skF_3',A_288)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_288)
      | ~ v2_pre_topc(A_288)
      | v2_struct_0(A_288) ) ),
    inference(resolution,[status(thm)],[c_48,c_286])).

tff(c_297,plain,(
    ! [E_286,D_287,A_288] :
      ( r2_hidden('#skF_1'(E_286,D_287,A_288,'#skF_3','#skF_2','#skF_4'),u1_struct_0('#skF_3'))
      | r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1(A_288,'#skF_2',D_287,'#skF_3',E_286),'#skF_4')
      | ~ m1_pre_topc('#skF_3',D_287)
      | ~ m1_subset_1(E_286,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_287),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_286,u1_struct_0(D_287),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_286)
      | ~ m1_pre_topc(D_287,A_288)
      | v2_struct_0(D_287)
      | ~ m1_pre_topc('#skF_3',A_288)
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_288)
      | ~ v2_pre_topc(A_288)
      | v2_struct_0(A_288) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_52,c_50,c_292])).

tff(c_299,plain,(
    ! [E_292,D_293,A_294] :
      ( r2_hidden('#skF_1'(E_292,D_293,A_294,'#skF_3','#skF_2','#skF_4'),u1_struct_0('#skF_3'))
      | r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1(A_294,'#skF_2',D_293,'#skF_3',E_292),'#skF_4')
      | ~ m1_pre_topc('#skF_3',D_293)
      | ~ m1_subset_1(E_292,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_293),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_292,u1_struct_0(D_293),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_292)
      | ~ m1_pre_topc(D_293,A_294)
      | v2_struct_0(D_293)
      | ~ m1_pre_topc('#skF_3',A_294)
      | ~ l1_pre_topc(A_294)
      | ~ v2_pre_topc(A_294)
      | v2_struct_0(A_294) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_56,c_297])).

tff(c_307,plain,(
    ! [A_294] :
      ( r2_hidden('#skF_1'('#skF_4','#skF_3',A_294,'#skF_3','#skF_2','#skF_4'),u1_struct_0('#skF_3'))
      | r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1(A_294,'#skF_2','#skF_3','#skF_3','#skF_4'),'#skF_4')
      | ~ m1_pre_topc('#skF_3','#skF_3')
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_4')
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc('#skF_3',A_294)
      | ~ l1_pre_topc(A_294)
      | ~ v2_pre_topc(A_294)
      | v2_struct_0(A_294) ) ),
    inference(resolution,[status(thm)],[c_48,c_299])).

tff(c_318,plain,(
    ! [A_294] :
      ( r2_hidden('#skF_1'('#skF_4','#skF_3',A_294,'#skF_3','#skF_2','#skF_4'),u1_struct_0('#skF_3'))
      | r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1(A_294,'#skF_2','#skF_3','#skF_3','#skF_4'),'#skF_4')
      | ~ m1_pre_topc('#skF_3','#skF_3')
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc('#skF_3',A_294)
      | ~ l1_pre_topc(A_294)
      | ~ v2_pre_topc(A_294)
      | v2_struct_0(A_294) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_307])).

tff(c_319,plain,(
    ! [A_294] :
      ( r2_hidden('#skF_1'('#skF_4','#skF_3',A_294,'#skF_3','#skF_2','#skF_4'),u1_struct_0('#skF_3'))
      | r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1(A_294,'#skF_2','#skF_3','#skF_3','#skF_4'),'#skF_4')
      | ~ m1_pre_topc('#skF_3','#skF_3')
      | ~ m1_pre_topc('#skF_3',A_294)
      | ~ l1_pre_topc(A_294)
      | ~ v2_pre_topc(A_294)
      | v2_struct_0(A_294) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_318])).

tff(c_320,plain,(
    ~ m1_pre_topc('#skF_3','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_319])).

tff(c_323,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_320])).

tff(c_327,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_323])).

tff(c_329,plain,(
    m1_pre_topc('#skF_3','#skF_3') ),
    inference(splitRight,[status(thm)],[c_319])).

tff(c_154,plain,(
    ! [D_242,A_243,C_239,E_240,B_241] :
      ( v1_funct_1(k3_tmap_1(A_243,B_241,C_239,D_242,E_240))
      | ~ m1_subset_1(E_240,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_239),u1_struct_0(B_241))))
      | ~ v1_funct_2(E_240,u1_struct_0(C_239),u1_struct_0(B_241))
      | ~ v1_funct_1(E_240)
      | ~ m1_pre_topc(D_242,A_243)
      | ~ m1_pre_topc(C_239,A_243)
      | ~ l1_pre_topc(B_241)
      | ~ v2_pre_topc(B_241)
      | v2_struct_0(B_241)
      | ~ l1_pre_topc(A_243)
      | ~ v2_pre_topc(A_243)
      | v2_struct_0(A_243) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_158,plain,(
    ! [A_243,D_242] :
      ( v1_funct_1(k3_tmap_1(A_243,'#skF_2','#skF_3',D_242,'#skF_4'))
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_4')
      | ~ m1_pre_topc(D_242,A_243)
      | ~ m1_pre_topc('#skF_3',A_243)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_243)
      | ~ v2_pre_topc(A_243)
      | v2_struct_0(A_243) ) ),
    inference(resolution,[status(thm)],[c_48,c_154])).

tff(c_162,plain,(
    ! [A_243,D_242] :
      ( v1_funct_1(k3_tmap_1(A_243,'#skF_2','#skF_3',D_242,'#skF_4'))
      | ~ m1_pre_topc(D_242,A_243)
      | ~ m1_pre_topc('#skF_3',A_243)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_243)
      | ~ v2_pre_topc(A_243)
      | v2_struct_0(A_243) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_52,c_50,c_158])).

tff(c_163,plain,(
    ! [A_243,D_242] :
      ( v1_funct_1(k3_tmap_1(A_243,'#skF_2','#skF_3',D_242,'#skF_4'))
      | ~ m1_pre_topc(D_242,A_243)
      | ~ m1_pre_topc('#skF_3',A_243)
      | ~ l1_pre_topc(A_243)
      | ~ v2_pre_topc(A_243)
      | v2_struct_0(A_243) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_162])).

tff(c_164,plain,(
    ! [C_244,E_245,D_247,A_248,B_246] :
      ( v1_funct_2(k3_tmap_1(A_248,B_246,C_244,D_247,E_245),u1_struct_0(D_247),u1_struct_0(B_246))
      | ~ m1_subset_1(E_245,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_244),u1_struct_0(B_246))))
      | ~ v1_funct_2(E_245,u1_struct_0(C_244),u1_struct_0(B_246))
      | ~ v1_funct_1(E_245)
      | ~ m1_pre_topc(D_247,A_248)
      | ~ m1_pre_topc(C_244,A_248)
      | ~ l1_pre_topc(B_246)
      | ~ v2_pre_topc(B_246)
      | v2_struct_0(B_246)
      | ~ l1_pre_topc(A_248)
      | ~ v2_pre_topc(A_248)
      | v2_struct_0(A_248) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_168,plain,(
    ! [A_248,D_247] :
      ( v1_funct_2(k3_tmap_1(A_248,'#skF_2','#skF_3',D_247,'#skF_4'),u1_struct_0(D_247),u1_struct_0('#skF_2'))
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_4')
      | ~ m1_pre_topc(D_247,A_248)
      | ~ m1_pre_topc('#skF_3',A_248)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_248)
      | ~ v2_pre_topc(A_248)
      | v2_struct_0(A_248) ) ),
    inference(resolution,[status(thm)],[c_48,c_164])).

tff(c_172,plain,(
    ! [A_248,D_247] :
      ( v1_funct_2(k3_tmap_1(A_248,'#skF_2','#skF_3',D_247,'#skF_4'),u1_struct_0(D_247),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_247,A_248)
      | ~ m1_pre_topc('#skF_3',A_248)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_248)
      | ~ v2_pre_topc(A_248)
      | v2_struct_0(A_248) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_52,c_50,c_168])).

tff(c_173,plain,(
    ! [A_248,D_247] :
      ( v1_funct_2(k3_tmap_1(A_248,'#skF_2','#skF_3',D_247,'#skF_4'),u1_struct_0(D_247),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_247,A_248)
      | ~ m1_pre_topc('#skF_3',A_248)
      | ~ l1_pre_topc(A_248)
      | ~ v2_pre_topc(A_248)
      | v2_struct_0(A_248) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_172])).

tff(c_18,plain,(
    ! [A_23,B_24,D_26,C_25,E_27] :
      ( m1_subset_1(k3_tmap_1(A_23,B_24,C_25,D_26,E_27),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_26),u1_struct_0(B_24))))
      | ~ m1_subset_1(E_27,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_25),u1_struct_0(B_24))))
      | ~ v1_funct_2(E_27,u1_struct_0(C_25),u1_struct_0(B_24))
      | ~ v1_funct_1(E_27)
      | ~ m1_pre_topc(D_26,A_23)
      | ~ m1_pre_topc(C_25,A_23)
      | ~ l1_pre_topc(B_24)
      | ~ v2_pre_topc(B_24)
      | v2_struct_0(B_24)
      | ~ l1_pre_topc(A_23)
      | ~ v2_pre_topc(A_23)
      | v2_struct_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_182,plain,(
    ! [C_261,B_262,D_263,A_264] :
      ( r2_funct_2(u1_struct_0(C_261),u1_struct_0(B_262),D_263,k3_tmap_1(A_264,B_262,C_261,C_261,D_263))
      | ~ m1_subset_1(D_263,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_261),u1_struct_0(B_262))))
      | ~ v1_funct_2(D_263,u1_struct_0(C_261),u1_struct_0(B_262))
      | ~ v1_funct_1(D_263)
      | ~ m1_pre_topc(C_261,A_264)
      | v2_struct_0(C_261)
      | ~ l1_pre_topc(B_262)
      | ~ v2_pre_topc(B_262)
      | v2_struct_0(B_262)
      | ~ l1_pre_topc(A_264)
      | ~ v2_pre_topc(A_264)
      | v2_struct_0(A_264) ) ),
    inference(cnfTransformation,[status(thm)],[f_226])).

tff(c_186,plain,(
    ! [A_264] :
      ( r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',k3_tmap_1(A_264,'#skF_2','#skF_3','#skF_3','#skF_4'))
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_4')
      | ~ m1_pre_topc('#skF_3',A_264)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_264)
      | ~ v2_pre_topc(A_264)
      | v2_struct_0(A_264) ) ),
    inference(resolution,[status(thm)],[c_48,c_182])).

tff(c_190,plain,(
    ! [A_264] :
      ( r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',k3_tmap_1(A_264,'#skF_2','#skF_3','#skF_3','#skF_4'))
      | ~ m1_pre_topc('#skF_3',A_264)
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_264)
      | ~ v2_pre_topc(A_264)
      | v2_struct_0(A_264) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_52,c_50,c_186])).

tff(c_192,plain,(
    ! [A_265] :
      ( r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',k3_tmap_1(A_265,'#skF_2','#skF_3','#skF_3','#skF_4'))
      | ~ m1_pre_topc('#skF_3',A_265)
      | ~ l1_pre_topc(A_265)
      | ~ v2_pre_topc(A_265)
      | v2_struct_0(A_265) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_56,c_190])).

tff(c_8,plain,(
    ! [D_10,C_9,A_7,B_8] :
      ( D_10 = C_9
      | ~ r2_funct_2(A_7,B_8,C_9,D_10)
      | ~ m1_subset_1(D_10,k1_zfmisc_1(k2_zfmisc_1(A_7,B_8)))
      | ~ v1_funct_2(D_10,A_7,B_8)
      | ~ v1_funct_1(D_10)
      | ~ m1_subset_1(C_9,k1_zfmisc_1(k2_zfmisc_1(A_7,B_8)))
      | ~ v1_funct_2(C_9,A_7,B_8)
      | ~ v1_funct_1(C_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_194,plain,(
    ! [A_265] :
      ( k3_tmap_1(A_265,'#skF_2','#skF_3','#skF_3','#skF_4') = '#skF_4'
      | ~ m1_subset_1(k3_tmap_1(A_265,'#skF_2','#skF_3','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(k3_tmap_1(A_265,'#skF_2','#skF_3','#skF_3','#skF_4'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k3_tmap_1(A_265,'#skF_2','#skF_3','#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_4')
      | ~ m1_pre_topc('#skF_3',A_265)
      | ~ l1_pre_topc(A_265)
      | ~ v2_pre_topc(A_265)
      | v2_struct_0(A_265) ) ),
    inference(resolution,[status(thm)],[c_192,c_8])).

tff(c_215,plain,(
    ! [A_275] :
      ( k3_tmap_1(A_275,'#skF_2','#skF_3','#skF_3','#skF_4') = '#skF_4'
      | ~ m1_subset_1(k3_tmap_1(A_275,'#skF_2','#skF_3','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(k3_tmap_1(A_275,'#skF_2','#skF_3','#skF_3','#skF_4'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k3_tmap_1(A_275,'#skF_2','#skF_3','#skF_3','#skF_4'))
      | ~ m1_pre_topc('#skF_3',A_275)
      | ~ l1_pre_topc(A_275)
      | ~ v2_pre_topc(A_275)
      | v2_struct_0(A_275) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_194])).

tff(c_219,plain,(
    ! [A_23] :
      ( k3_tmap_1(A_23,'#skF_2','#skF_3','#skF_3','#skF_4') = '#skF_4'
      | ~ v1_funct_2(k3_tmap_1(A_23,'#skF_2','#skF_3','#skF_3','#skF_4'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k3_tmap_1(A_23,'#skF_2','#skF_3','#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_4')
      | ~ m1_pre_topc('#skF_3',A_23)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_23)
      | ~ v2_pre_topc(A_23)
      | v2_struct_0(A_23) ) ),
    inference(resolution,[status(thm)],[c_18,c_215])).

tff(c_222,plain,(
    ! [A_23] :
      ( k3_tmap_1(A_23,'#skF_2','#skF_3','#skF_3','#skF_4') = '#skF_4'
      | ~ v1_funct_2(k3_tmap_1(A_23,'#skF_2','#skF_3','#skF_3','#skF_4'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k3_tmap_1(A_23,'#skF_2','#skF_3','#skF_3','#skF_4'))
      | ~ m1_pre_topc('#skF_3',A_23)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_23)
      | ~ v2_pre_topc(A_23)
      | v2_struct_0(A_23) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_52,c_50,c_48,c_219])).

tff(c_224,plain,(
    ! [A_276] :
      ( k3_tmap_1(A_276,'#skF_2','#skF_3','#skF_3','#skF_4') = '#skF_4'
      | ~ v1_funct_2(k3_tmap_1(A_276,'#skF_2','#skF_3','#skF_3','#skF_4'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k3_tmap_1(A_276,'#skF_2','#skF_3','#skF_3','#skF_4'))
      | ~ m1_pre_topc('#skF_3',A_276)
      | ~ l1_pre_topc(A_276)
      | ~ v2_pre_topc(A_276)
      | v2_struct_0(A_276) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_222])).

tff(c_230,plain,(
    ! [A_277] :
      ( k3_tmap_1(A_277,'#skF_2','#skF_3','#skF_3','#skF_4') = '#skF_4'
      | ~ v1_funct_1(k3_tmap_1(A_277,'#skF_2','#skF_3','#skF_3','#skF_4'))
      | ~ m1_pre_topc('#skF_3',A_277)
      | ~ l1_pre_topc(A_277)
      | ~ v2_pre_topc(A_277)
      | v2_struct_0(A_277) ) ),
    inference(resolution,[status(thm)],[c_173,c_224])).

tff(c_236,plain,(
    ! [A_278] :
      ( k3_tmap_1(A_278,'#skF_2','#skF_3','#skF_3','#skF_4') = '#skF_4'
      | ~ m1_pre_topc('#skF_3',A_278)
      | ~ l1_pre_topc(A_278)
      | ~ v2_pre_topc(A_278)
      | v2_struct_0(A_278) ) ),
    inference(resolution,[status(thm)],[c_163,c_230])).

tff(c_243,plain,
    ( k3_tmap_1('#skF_2','#skF_2','#skF_3','#skF_3','#skF_4') = '#skF_4'
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_236])).

tff(c_250,plain,
    ( k3_tmap_1('#skF_2','#skF_2','#skF_3','#skF_3','#skF_4') = '#skF_4'
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_243])).

tff(c_251,plain,(
    k3_tmap_1('#skF_2','#skF_2','#skF_3','#skF_3','#skF_4') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_250])).

tff(c_403,plain,(
    ! [F_319,C_317,D_315,B_318,E_314,A_316] :
      ( m1_subset_1('#skF_1'(E_314,D_315,A_316,C_317,B_318,F_319),u1_struct_0(D_315))
      | r2_funct_2(u1_struct_0(C_317),u1_struct_0(B_318),k3_tmap_1(A_316,B_318,D_315,C_317,E_314),F_319)
      | ~ m1_subset_1(F_319,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_317),u1_struct_0(B_318))))
      | ~ v1_funct_2(F_319,u1_struct_0(C_317),u1_struct_0(B_318))
      | ~ v1_funct_1(F_319)
      | ~ m1_pre_topc(C_317,D_315)
      | ~ m1_subset_1(E_314,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_315),u1_struct_0(B_318))))
      | ~ v1_funct_2(E_314,u1_struct_0(D_315),u1_struct_0(B_318))
      | ~ v1_funct_1(E_314)
      | ~ m1_pre_topc(D_315,A_316)
      | v2_struct_0(D_315)
      | ~ m1_pre_topc(C_317,A_316)
      | v2_struct_0(C_317)
      | ~ l1_pre_topc(B_318)
      | ~ v2_pre_topc(B_318)
      | v2_struct_0(B_318)
      | ~ l1_pre_topc(A_316)
      | ~ v2_pre_topc(A_316)
      | v2_struct_0(A_316) ) ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_567,plain,(
    ! [B_381,A_379,E_380,D_378,A_382] :
      ( m1_subset_1('#skF_1'(E_380,D_378,A_382,B_381,A_379,k4_tmap_1(A_379,B_381)),u1_struct_0(D_378))
      | r2_funct_2(u1_struct_0(B_381),u1_struct_0(A_379),k3_tmap_1(A_382,A_379,D_378,B_381,E_380),k4_tmap_1(A_379,B_381))
      | ~ v1_funct_2(k4_tmap_1(A_379,B_381),u1_struct_0(B_381),u1_struct_0(A_379))
      | ~ v1_funct_1(k4_tmap_1(A_379,B_381))
      | ~ m1_pre_topc(B_381,D_378)
      | ~ m1_subset_1(E_380,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_378),u1_struct_0(A_379))))
      | ~ v1_funct_2(E_380,u1_struct_0(D_378),u1_struct_0(A_379))
      | ~ v1_funct_1(E_380)
      | ~ m1_pre_topc(D_378,A_382)
      | v2_struct_0(D_378)
      | ~ m1_pre_topc(B_381,A_382)
      | v2_struct_0(B_381)
      | ~ l1_pre_topc(A_382)
      | ~ v2_pre_topc(A_382)
      | v2_struct_0(A_382)
      | ~ m1_pre_topc(B_381,A_379)
      | ~ l1_pre_topc(A_379)
      | ~ v2_pre_topc(A_379)
      | v2_struct_0(A_379) ) ),
    inference(resolution,[status(thm)],[c_24,c_403])).

tff(c_580,plain,
    ( m1_subset_1('#skF_1'('#skF_4','#skF_3','#skF_2','#skF_3','#skF_2',k4_tmap_1('#skF_2','#skF_3')),u1_struct_0('#skF_3'))
    | r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',k4_tmap_1('#skF_2','#skF_3'))
    | ~ v1_funct_2(k4_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k4_tmap_1('#skF_2','#skF_3'))
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_251,c_567])).

tff(c_586,plain,
    ( m1_subset_1('#skF_1'('#skF_4','#skF_3','#skF_2','#skF_3','#skF_2',k4_tmap_1('#skF_2','#skF_3')),u1_struct_0('#skF_3'))
    | r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',k4_tmap_1('#skF_2','#skF_3'))
    | ~ v1_funct_2(k4_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k4_tmap_1('#skF_2','#skF_3'))
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_54,c_60,c_58,c_54,c_54,c_52,c_50,c_48,c_329,c_580])).

tff(c_587,plain,
    ( m1_subset_1('#skF_1'('#skF_4','#skF_3','#skF_2','#skF_3','#skF_2',k4_tmap_1('#skF_2','#skF_3')),u1_struct_0('#skF_3'))
    | r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',k4_tmap_1('#skF_2','#skF_3'))
    | ~ v1_funct_2(k4_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k4_tmap_1('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_56,c_586])).

tff(c_588,plain,(
    ~ v1_funct_1(k4_tmap_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_587])).

tff(c_591,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_588])).

tff(c_594,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_54,c_591])).

tff(c_596,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_594])).

tff(c_598,plain,(
    v1_funct_1(k4_tmap_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_587])).

tff(c_26,plain,(
    ! [A_28,B_29] :
      ( v1_funct_2(k4_tmap_1(A_28,B_29),u1_struct_0(B_29),u1_struct_0(A_28))
      | ~ m1_pre_topc(B_29,A_28)
      | ~ l1_pre_topc(A_28)
      | ~ v2_pre_topc(A_28)
      | v2_struct_0(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_597,plain,
    ( ~ v1_funct_2(k4_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',k4_tmap_1('#skF_2','#skF_3'))
    | m1_subset_1('#skF_1'('#skF_4','#skF_3','#skF_2','#skF_3','#skF_2',k4_tmap_1('#skF_2','#skF_3')),u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_587])).

tff(c_599,plain,(
    ~ v1_funct_2(k4_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_597])).

tff(c_612,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_599])).

tff(c_615,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_54,c_612])).

tff(c_617,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_615])).

tff(c_619,plain,(
    v1_funct_2(k4_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_597])).

tff(c_618,plain,
    ( m1_subset_1('#skF_1'('#skF_4','#skF_3','#skF_2','#skF_3','#skF_2',k4_tmap_1('#skF_2','#skF_3')),u1_struct_0('#skF_3'))
    | r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',k4_tmap_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_597])).

tff(c_620,plain,(
    r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',k4_tmap_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_618])).

tff(c_635,plain,
    ( k4_tmap_1('#skF_2','#skF_3') = '#skF_4'
    | ~ m1_subset_1(k4_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k4_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k4_tmap_1('#skF_2','#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_620,c_8])).

tff(c_638,plain,
    ( k4_tmap_1('#skF_2','#skF_3') = '#skF_4'
    | ~ m1_subset_1(k4_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_598,c_619,c_635])).

tff(c_639,plain,(
    ~ m1_subset_1(k4_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_638])).

tff(c_642,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_639])).

tff(c_645,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_54,c_642])).

tff(c_647,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_645])).

tff(c_648,plain,(
    k4_tmap_1('#skF_2','#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_638])).

tff(c_44,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k4_tmap_1('#skF_2','#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_288])).

tff(c_653,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_648,c_44])).

tff(c_659,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_653])).

tff(c_661,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',k4_tmap_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_618])).

tff(c_660,plain,(
    m1_subset_1('#skF_1'('#skF_4','#skF_3','#skF_2','#skF_3','#skF_2',k4_tmap_1('#skF_2','#skF_3')),u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_618])).

tff(c_16,plain,(
    ! [C_22,A_16,B_20] :
      ( m1_subset_1(C_22,u1_struct_0(A_16))
      | ~ m1_subset_1(C_22,u1_struct_0(B_20))
      | ~ m1_pre_topc(B_20,A_16)
      | v2_struct_0(B_20)
      | ~ l1_pre_topc(A_16)
      | v2_struct_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_677,plain,(
    ! [A_16] :
      ( m1_subset_1('#skF_1'('#skF_4','#skF_3','#skF_2','#skF_3','#skF_2',k4_tmap_1('#skF_2','#skF_3')),u1_struct_0(A_16))
      | ~ m1_pre_topc('#skF_3',A_16)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_16)
      | v2_struct_0(A_16) ) ),
    inference(resolution,[status(thm)],[c_660,c_16])).

tff(c_697,plain,(
    ! [A_397] :
      ( m1_subset_1('#skF_1'('#skF_4','#skF_3','#skF_2','#skF_3','#skF_2',k4_tmap_1('#skF_2','#skF_3')),u1_struct_0(A_397))
      | ~ m1_pre_topc('#skF_3',A_397)
      | ~ l1_pre_topc(A_397)
      | v2_struct_0(A_397) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_677])).

tff(c_114,plain,(
    ! [A_1] :
      ( k1_funct_1('#skF_4',A_1) = A_1
      | ~ m1_subset_1(A_1,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(A_1,u1_struct_0('#skF_3')) ) ),
    inference(splitRight,[status(thm)],[c_83])).

tff(c_707,plain,
    ( k1_funct_1('#skF_4','#skF_1'('#skF_4','#skF_3','#skF_2','#skF_3','#skF_2',k4_tmap_1('#skF_2','#skF_3'))) = '#skF_1'('#skF_4','#skF_3','#skF_2','#skF_3','#skF_2',k4_tmap_1('#skF_2','#skF_3'))
    | ~ m1_subset_1('#skF_1'('#skF_4','#skF_3','#skF_2','#skF_3','#skF_2',k4_tmap_1('#skF_2','#skF_3')),u1_struct_0('#skF_3'))
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_697,c_114])).

tff(c_713,plain,
    ( k1_funct_1('#skF_4','#skF_1'('#skF_4','#skF_3','#skF_2','#skF_3','#skF_2',k4_tmap_1('#skF_2','#skF_3'))) = '#skF_1'('#skF_4','#skF_3','#skF_2','#skF_3','#skF_2',k4_tmap_1('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_54,c_660,c_707])).

tff(c_714,plain,(
    k1_funct_1('#skF_4','#skF_1'('#skF_4','#skF_3','#skF_2','#skF_3','#skF_2',k4_tmap_1('#skF_2','#skF_3'))) = '#skF_1'('#skF_4','#skF_3','#skF_2','#skF_3','#skF_2',k4_tmap_1('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_713])).

tff(c_4,plain,(
    ! [A_3,B_4,C_5,D_6] :
      ( k3_funct_2(A_3,B_4,C_5,D_6) = k1_funct_1(C_5,D_6)
      | ~ m1_subset_1(D_6,A_3)
      | ~ m1_subset_1(C_5,k1_zfmisc_1(k2_zfmisc_1(A_3,B_4)))
      | ~ v1_funct_2(C_5,A_3,B_4)
      | ~ v1_funct_1(C_5)
      | v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_675,plain,(
    ! [B_4,C_5] :
      ( k3_funct_2(u1_struct_0('#skF_3'),B_4,C_5,'#skF_1'('#skF_4','#skF_3','#skF_2','#skF_3','#skF_2',k4_tmap_1('#skF_2','#skF_3'))) = k1_funct_1(C_5,'#skF_1'('#skF_4','#skF_3','#skF_2','#skF_3','#skF_2',k4_tmap_1('#skF_2','#skF_3')))
      | ~ m1_subset_1(C_5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),B_4)))
      | ~ v1_funct_2(C_5,u1_struct_0('#skF_3'),B_4)
      | ~ v1_funct_1(C_5)
      | v1_xboole_0(u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_660,c_4])).

tff(c_807,plain,(
    ! [B_409,C_410] :
      ( k3_funct_2(u1_struct_0('#skF_3'),B_409,C_410,'#skF_1'('#skF_4','#skF_3','#skF_2','#skF_3','#skF_2',k4_tmap_1('#skF_2','#skF_3'))) = k1_funct_1(C_410,'#skF_1'('#skF_4','#skF_3','#skF_2','#skF_3','#skF_2',k4_tmap_1('#skF_2','#skF_3')))
      | ~ m1_subset_1(C_410,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),B_409)))
      | ~ v1_funct_2(C_410,u1_struct_0('#skF_3'),B_409)
      | ~ v1_funct_1(C_410) ) ),
    inference(negUnitSimplification,[status(thm)],[c_115,c_675])).

tff(c_818,plain,
    ( k3_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4','#skF_1'('#skF_4','#skF_3','#skF_2','#skF_3','#skF_2',k4_tmap_1('#skF_2','#skF_3'))) = k1_funct_1('#skF_4','#skF_1'('#skF_4','#skF_3','#skF_2','#skF_3','#skF_2',k4_tmap_1('#skF_2','#skF_3')))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_807])).

tff(c_823,plain,(
    k3_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4','#skF_1'('#skF_4','#skF_3','#skF_2','#skF_3','#skF_2',k4_tmap_1('#skF_2','#skF_3'))) = '#skF_1'('#skF_4','#skF_3','#skF_2','#skF_3','#skF_2',k4_tmap_1('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_714,c_818])).

tff(c_32,plain,(
    ! [E_151,A_31,B_95,F_155,D_143,C_127] :
      ( k3_funct_2(u1_struct_0(D_143),u1_struct_0(B_95),E_151,'#skF_1'(E_151,D_143,A_31,C_127,B_95,F_155)) != k1_funct_1(F_155,'#skF_1'(E_151,D_143,A_31,C_127,B_95,F_155))
      | r2_funct_2(u1_struct_0(C_127),u1_struct_0(B_95),k3_tmap_1(A_31,B_95,D_143,C_127,E_151),F_155)
      | ~ m1_subset_1(F_155,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_127),u1_struct_0(B_95))))
      | ~ v1_funct_2(F_155,u1_struct_0(C_127),u1_struct_0(B_95))
      | ~ v1_funct_1(F_155)
      | ~ m1_pre_topc(C_127,D_143)
      | ~ m1_subset_1(E_151,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_143),u1_struct_0(B_95))))
      | ~ v1_funct_2(E_151,u1_struct_0(D_143),u1_struct_0(B_95))
      | ~ v1_funct_1(E_151)
      | ~ m1_pre_topc(D_143,A_31)
      | v2_struct_0(D_143)
      | ~ m1_pre_topc(C_127,A_31)
      | v2_struct_0(C_127)
      | ~ l1_pre_topc(B_95)
      | ~ v2_pre_topc(B_95)
      | v2_struct_0(B_95)
      | ~ l1_pre_topc(A_31)
      | ~ v2_pre_topc(A_31)
      | v2_struct_0(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_826,plain,
    ( k1_funct_1(k4_tmap_1('#skF_2','#skF_3'),'#skF_1'('#skF_4','#skF_3','#skF_2','#skF_3','#skF_2',k4_tmap_1('#skF_2','#skF_3'))) != '#skF_1'('#skF_4','#skF_3','#skF_2','#skF_3','#skF_2',k4_tmap_1('#skF_2','#skF_3'))
    | r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_2','#skF_2','#skF_3','#skF_3','#skF_4'),k4_tmap_1('#skF_2','#skF_3'))
    | ~ m1_subset_1(k4_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k4_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k4_tmap_1('#skF_2','#skF_3'))
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_823,c_32])).

tff(c_830,plain,
    ( k1_funct_1(k4_tmap_1('#skF_2','#skF_3'),'#skF_1'('#skF_4','#skF_3','#skF_2','#skF_3','#skF_2',k4_tmap_1('#skF_2','#skF_3'))) != '#skF_1'('#skF_4','#skF_3','#skF_2','#skF_3','#skF_2',k4_tmap_1('#skF_2','#skF_3'))
    | r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',k4_tmap_1('#skF_2','#skF_3'))
    | ~ m1_subset_1(k4_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_60,c_58,c_54,c_54,c_52,c_50,c_48,c_329,c_598,c_619,c_251,c_826])).

tff(c_831,plain,
    ( k1_funct_1(k4_tmap_1('#skF_2','#skF_3'),'#skF_1'('#skF_4','#skF_3','#skF_2','#skF_3','#skF_2',k4_tmap_1('#skF_2','#skF_3'))) != '#skF_1'('#skF_4','#skF_3','#skF_2','#skF_3','#skF_2',k4_tmap_1('#skF_2','#skF_3'))
    | ~ m1_subset_1(k4_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_56,c_661,c_830])).

tff(c_833,plain,(
    ~ m1_subset_1(k4_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_831])).

tff(c_860,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_833])).

tff(c_863,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_54,c_860])).

tff(c_865,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_863])).

tff(c_866,plain,(
    k1_funct_1(k4_tmap_1('#skF_2','#skF_3'),'#skF_1'('#skF_4','#skF_3','#skF_2','#skF_3','#skF_2',k4_tmap_1('#skF_2','#skF_3'))) != '#skF_1'('#skF_4','#skF_3','#skF_2','#skF_3','#skF_2',k4_tmap_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_831])).

tff(c_719,plain,(
    ! [A_398,A_399] :
      ( m1_subset_1('#skF_1'('#skF_4','#skF_3','#skF_2','#skF_3','#skF_2',k4_tmap_1('#skF_2','#skF_3')),u1_struct_0(A_398))
      | ~ m1_pre_topc(A_399,A_398)
      | ~ l1_pre_topc(A_398)
      | v2_struct_0(A_398)
      | ~ m1_pre_topc('#skF_3',A_399)
      | ~ l1_pre_topc(A_399)
      | v2_struct_0(A_399) ) ),
    inference(resolution,[status(thm)],[c_697,c_16])).

tff(c_725,plain,
    ( m1_subset_1('#skF_1'('#skF_4','#skF_3','#skF_2','#skF_3','#skF_2',k4_tmap_1('#skF_2','#skF_3')),u1_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_719])).

tff(c_733,plain,
    ( m1_subset_1('#skF_1'('#skF_4','#skF_3','#skF_2','#skF_3','#skF_2',k4_tmap_1('#skF_2','#skF_3')),u1_struct_0('#skF_2'))
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_329,c_58,c_725])).

tff(c_734,plain,(
    m1_subset_1('#skF_1'('#skF_4','#skF_3','#skF_2','#skF_3','#skF_2',k4_tmap_1('#skF_2','#skF_3')),u1_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_62,c_733])).

tff(c_129,plain,(
    ! [A_223,B_224,C_225] :
      ( k1_funct_1(k4_tmap_1(A_223,B_224),C_225) = C_225
      | ~ r2_hidden(C_225,u1_struct_0(B_224))
      | ~ m1_subset_1(C_225,u1_struct_0(A_223))
      | ~ m1_pre_topc(B_224,A_223)
      | v2_struct_0(B_224)
      | ~ l1_pre_topc(A_223)
      | ~ v2_pre_topc(A_223)
      | v2_struct_0(A_223) ) ),
    inference(cnfTransformation,[status(thm)],[f_258])).

tff(c_133,plain,(
    ! [A_223,B_224,A_1] :
      ( k1_funct_1(k4_tmap_1(A_223,B_224),A_1) = A_1
      | ~ m1_subset_1(A_1,u1_struct_0(A_223))
      | ~ m1_pre_topc(B_224,A_223)
      | v2_struct_0(B_224)
      | ~ l1_pre_topc(A_223)
      | ~ v2_pre_topc(A_223)
      | v2_struct_0(A_223)
      | v1_xboole_0(u1_struct_0(B_224))
      | ~ m1_subset_1(A_1,u1_struct_0(B_224)) ) ),
    inference(resolution,[status(thm)],[c_2,c_129])).

tff(c_736,plain,(
    ! [B_224] :
      ( k1_funct_1(k4_tmap_1('#skF_2',B_224),'#skF_1'('#skF_4','#skF_3','#skF_2','#skF_3','#skF_2',k4_tmap_1('#skF_2','#skF_3'))) = '#skF_1'('#skF_4','#skF_3','#skF_2','#skF_3','#skF_2',k4_tmap_1('#skF_2','#skF_3'))
      | ~ m1_pre_topc(B_224,'#skF_2')
      | v2_struct_0(B_224)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | v1_xboole_0(u1_struct_0(B_224))
      | ~ m1_subset_1('#skF_1'('#skF_4','#skF_3','#skF_2','#skF_3','#skF_2',k4_tmap_1('#skF_2','#skF_3')),u1_struct_0(B_224)) ) ),
    inference(resolution,[status(thm)],[c_734,c_133])).

tff(c_746,plain,(
    ! [B_224] :
      ( k1_funct_1(k4_tmap_1('#skF_2',B_224),'#skF_1'('#skF_4','#skF_3','#skF_2','#skF_3','#skF_2',k4_tmap_1('#skF_2','#skF_3'))) = '#skF_1'('#skF_4','#skF_3','#skF_2','#skF_3','#skF_2',k4_tmap_1('#skF_2','#skF_3'))
      | ~ m1_pre_topc(B_224,'#skF_2')
      | v2_struct_0(B_224)
      | v2_struct_0('#skF_2')
      | v1_xboole_0(u1_struct_0(B_224))
      | ~ m1_subset_1('#skF_1'('#skF_4','#skF_3','#skF_2','#skF_3','#skF_2',k4_tmap_1('#skF_2','#skF_3')),u1_struct_0(B_224)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_736])).

tff(c_1005,plain,(
    ! [B_436] :
      ( k1_funct_1(k4_tmap_1('#skF_2',B_436),'#skF_1'('#skF_4','#skF_3','#skF_2','#skF_3','#skF_2',k4_tmap_1('#skF_2','#skF_3'))) = '#skF_1'('#skF_4','#skF_3','#skF_2','#skF_3','#skF_2',k4_tmap_1('#skF_2','#skF_3'))
      | ~ m1_pre_topc(B_436,'#skF_2')
      | v2_struct_0(B_436)
      | v1_xboole_0(u1_struct_0(B_436))
      | ~ m1_subset_1('#skF_1'('#skF_4','#skF_3','#skF_2','#skF_3','#skF_2',k4_tmap_1('#skF_2','#skF_3')),u1_struct_0(B_436)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_746])).

tff(c_1017,plain,
    ( k1_funct_1(k4_tmap_1('#skF_2','#skF_3'),'#skF_1'('#skF_4','#skF_3','#skF_2','#skF_3','#skF_2',k4_tmap_1('#skF_2','#skF_3'))) = '#skF_1'('#skF_4','#skF_3','#skF_2','#skF_3','#skF_2',k4_tmap_1('#skF_2','#skF_3'))
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | v2_struct_0('#skF_3')
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_660,c_1005])).

tff(c_1027,plain,
    ( k1_funct_1(k4_tmap_1('#skF_2','#skF_3'),'#skF_1'('#skF_4','#skF_3','#skF_2','#skF_3','#skF_2',k4_tmap_1('#skF_2','#skF_3'))) = '#skF_1'('#skF_4','#skF_3','#skF_2','#skF_3','#skF_2',k4_tmap_1('#skF_2','#skF_3'))
    | v2_struct_0('#skF_3')
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1017])).

tff(c_1029,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_115,c_56,c_866,c_1027])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:06:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.75/1.88  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.75/1.90  
% 4.75/1.90  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.15/1.90  %$ r2_funct_2 > v1_funct_2 > r2_hidden > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k3_funct_2 > k4_tmap_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 5.15/1.90  
% 5.15/1.90  %Foreground sorts:
% 5.15/1.90  
% 5.15/1.90  
% 5.15/1.90  %Background operators:
% 5.15/1.90  
% 5.15/1.90  
% 5.15/1.90  %Foreground operators:
% 5.15/1.90  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.15/1.90  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 5.15/1.90  tff(k4_tmap_1, type, k4_tmap_1: ($i * $i) > $i).
% 5.15/1.90  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.15/1.90  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.15/1.90  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i * $i) > $i).
% 5.15/1.90  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.15/1.90  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.15/1.90  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.15/1.90  tff('#skF_2', type, '#skF_2': $i).
% 5.15/1.90  tff('#skF_3', type, '#skF_3': $i).
% 5.15/1.90  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.15/1.90  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 5.15/1.90  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 5.15/1.90  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.15/1.90  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.15/1.90  tff('#skF_4', type, '#skF_4': $i).
% 5.15/1.90  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.15/1.90  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 5.15/1.90  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.15/1.90  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.15/1.90  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.15/1.90  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 5.15/1.90  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 5.15/1.90  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.15/1.90  
% 5.15/1.94  tff(f_288, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => ((![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, u1_struct_0(B)) => (D = k1_funct_1(C, D))))) => r2_funct_2(u1_struct_0(B), u1_struct_0(A), k4_tmap_1(A, B), C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t96_tmap_1)).
% 5.15/1.94  tff(f_71, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 5.15/1.94  tff(f_64, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 5.15/1.94  tff(f_31, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 5.15/1.94  tff(f_79, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 5.15/1.94  tff(f_140, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_pre_topc(B, A)) => ((v1_funct_1(k4_tmap_1(A, B)) & v1_funct_2(k4_tmap_1(A, B), u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(k4_tmap_1(A, B), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_tmap_1)).
% 5.15/1.94  tff(f_60, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_funct_2(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_funct_2)).
% 5.15/1.94  tff(f_144, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tsep_1)).
% 5.15/1.94  tff(f_196, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => (m1_pre_topc(C, D) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => ((![G]: (m1_subset_1(G, u1_struct_0(D)) => (r2_hidden(G, u1_struct_0(C)) => (k3_funct_2(u1_struct_0(D), u1_struct_0(B), E, G) = k1_funct_1(F, G))))) => r2_funct_2(u1_struct_0(C), u1_struct_0(B), k3_tmap_1(A, B, D, C, E), F))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_tmap_1)).
% 5.15/1.94  tff(f_125, axiom, (![A, B, C, D, E]: (((((((((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & ~v2_struct_0(B)) & v2_pre_topc(B)) & l1_pre_topc(B)) & m1_pre_topc(C, A)) & m1_pre_topc(D, A)) & v1_funct_1(E)) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => ((v1_funct_1(k3_tmap_1(A, B, C, D, E)) & v1_funct_2(k3_tmap_1(A, B, C, D, E), u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(k3_tmap_1(A, B, C, D, E), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_tmap_1)).
% 5.15/1.94  tff(f_226, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => r2_funct_2(u1_struct_0(C), u1_struct_0(B), D, k3_tmap_1(A, B, C, C, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_tmap_1)).
% 5.15/1.94  tff(f_95, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(B)) => m1_subset_1(C, u1_struct_0(A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_pre_topc)).
% 5.15/1.94  tff(f_44, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => (k3_funct_2(A, B, C, D) = k1_funct_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 5.15/1.94  tff(f_258, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(C, u1_struct_0(B)) => (k1_funct_1(k4_tmap_1(A, B), C) = C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_tmap_1)).
% 5.15/1.94  tff(c_58, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_288])).
% 5.15/1.94  tff(c_54, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_288])).
% 5.15/1.94  tff(c_65, plain, (![B_200, A_201]: (l1_pre_topc(B_200) | ~m1_pre_topc(B_200, A_201) | ~l1_pre_topc(A_201))), inference(cnfTransformation, [status(thm)], [f_71])).
% 5.15/1.94  tff(c_71, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_54, c_65])).
% 5.15/1.94  tff(c_75, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_71])).
% 5.15/1.94  tff(c_10, plain, (![A_11]: (l1_struct_0(A_11) | ~l1_pre_topc(A_11))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.15/1.94  tff(c_56, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_288])).
% 5.15/1.94  tff(c_2, plain, (![A_1, B_2]: (r2_hidden(A_1, B_2) | v1_xboole_0(B_2) | ~m1_subset_1(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.15/1.94  tff(c_78, plain, (![D_205]: (k1_funct_1('#skF_4', D_205)=D_205 | ~r2_hidden(D_205, u1_struct_0('#skF_3')) | ~m1_subset_1(D_205, u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_288])).
% 5.15/1.94  tff(c_83, plain, (![A_1]: (k1_funct_1('#skF_4', A_1)=A_1 | ~m1_subset_1(A_1, u1_struct_0('#skF_2')) | v1_xboole_0(u1_struct_0('#skF_3')) | ~m1_subset_1(A_1, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_2, c_78])).
% 5.15/1.94  tff(c_100, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_83])).
% 5.15/1.94  tff(c_14, plain, (![A_15]: (~v1_xboole_0(u1_struct_0(A_15)) | ~l1_struct_0(A_15) | v2_struct_0(A_15))), inference(cnfTransformation, [status(thm)], [f_79])).
% 5.15/1.94  tff(c_103, plain, (~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_100, c_14])).
% 5.15/1.94  tff(c_106, plain, (~l1_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_56, c_103])).
% 5.15/1.94  tff(c_109, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_10, c_106])).
% 5.15/1.94  tff(c_113, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_75, c_109])).
% 5.15/1.94  tff(c_115, plain, (~v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_83])).
% 5.15/1.94  tff(c_62, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_288])).
% 5.15/1.94  tff(c_60, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_288])).
% 5.15/1.94  tff(c_24, plain, (![A_28, B_29]: (m1_subset_1(k4_tmap_1(A_28, B_29), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_29), u1_struct_0(A_28)))) | ~m1_pre_topc(B_29, A_28) | ~l1_pre_topc(A_28) | ~v2_pre_topc(A_28) | v2_struct_0(A_28))), inference(cnfTransformation, [status(thm)], [f_140])).
% 5.15/1.94  tff(c_52, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_288])).
% 5.15/1.94  tff(c_50, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_288])).
% 5.15/1.94  tff(c_48, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_288])).
% 5.15/1.94  tff(c_119, plain, (![A_218, B_219, D_220]: (r2_funct_2(A_218, B_219, D_220, D_220) | ~m1_subset_1(D_220, k1_zfmisc_1(k2_zfmisc_1(A_218, B_219))) | ~v1_funct_2(D_220, A_218, B_219) | ~v1_funct_1(D_220))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.15/1.94  tff(c_121, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', '#skF_4') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_48, c_119])).
% 5.15/1.94  tff(c_124, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_121])).
% 5.15/1.94  tff(c_28, plain, (![A_28, B_29]: (v1_funct_1(k4_tmap_1(A_28, B_29)) | ~m1_pre_topc(B_29, A_28) | ~l1_pre_topc(A_28) | ~v2_pre_topc(A_28) | v2_struct_0(A_28))), inference(cnfTransformation, [status(thm)], [f_140])).
% 5.15/1.94  tff(c_30, plain, (![A_30]: (m1_pre_topc(A_30, A_30) | ~l1_pre_topc(A_30))), inference(cnfTransformation, [status(thm)], [f_144])).
% 5.15/1.94  tff(c_286, plain, (![A_288, E_286, C_289, B_290, D_287, F_291]: (r2_hidden('#skF_1'(E_286, D_287, A_288, C_289, B_290, F_291), u1_struct_0(C_289)) | r2_funct_2(u1_struct_0(C_289), u1_struct_0(B_290), k3_tmap_1(A_288, B_290, D_287, C_289, E_286), F_291) | ~m1_subset_1(F_291, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_289), u1_struct_0(B_290)))) | ~v1_funct_2(F_291, u1_struct_0(C_289), u1_struct_0(B_290)) | ~v1_funct_1(F_291) | ~m1_pre_topc(C_289, D_287) | ~m1_subset_1(E_286, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_287), u1_struct_0(B_290)))) | ~v1_funct_2(E_286, u1_struct_0(D_287), u1_struct_0(B_290)) | ~v1_funct_1(E_286) | ~m1_pre_topc(D_287, A_288) | v2_struct_0(D_287) | ~m1_pre_topc(C_289, A_288) | v2_struct_0(C_289) | ~l1_pre_topc(B_290) | ~v2_pre_topc(B_290) | v2_struct_0(B_290) | ~l1_pre_topc(A_288) | ~v2_pre_topc(A_288) | v2_struct_0(A_288))), inference(cnfTransformation, [status(thm)], [f_196])).
% 5.15/1.94  tff(c_292, plain, (![E_286, D_287, A_288]: (r2_hidden('#skF_1'(E_286, D_287, A_288, '#skF_3', '#skF_2', '#skF_4'), u1_struct_0('#skF_3')) | r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1(A_288, '#skF_2', D_287, '#skF_3', E_286), '#skF_4') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~m1_pre_topc('#skF_3', D_287) | ~m1_subset_1(E_286, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_287), u1_struct_0('#skF_2')))) | ~v1_funct_2(E_286, u1_struct_0(D_287), u1_struct_0('#skF_2')) | ~v1_funct_1(E_286) | ~m1_pre_topc(D_287, A_288) | v2_struct_0(D_287) | ~m1_pre_topc('#skF_3', A_288) | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_288) | ~v2_pre_topc(A_288) | v2_struct_0(A_288))), inference(resolution, [status(thm)], [c_48, c_286])).
% 5.15/1.94  tff(c_297, plain, (![E_286, D_287, A_288]: (r2_hidden('#skF_1'(E_286, D_287, A_288, '#skF_3', '#skF_2', '#skF_4'), u1_struct_0('#skF_3')) | r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1(A_288, '#skF_2', D_287, '#skF_3', E_286), '#skF_4') | ~m1_pre_topc('#skF_3', D_287) | ~m1_subset_1(E_286, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_287), u1_struct_0('#skF_2')))) | ~v1_funct_2(E_286, u1_struct_0(D_287), u1_struct_0('#skF_2')) | ~v1_funct_1(E_286) | ~m1_pre_topc(D_287, A_288) | v2_struct_0(D_287) | ~m1_pre_topc('#skF_3', A_288) | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_288) | ~v2_pre_topc(A_288) | v2_struct_0(A_288))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_52, c_50, c_292])).
% 5.15/1.94  tff(c_299, plain, (![E_292, D_293, A_294]: (r2_hidden('#skF_1'(E_292, D_293, A_294, '#skF_3', '#skF_2', '#skF_4'), u1_struct_0('#skF_3')) | r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1(A_294, '#skF_2', D_293, '#skF_3', E_292), '#skF_4') | ~m1_pre_topc('#skF_3', D_293) | ~m1_subset_1(E_292, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_293), u1_struct_0('#skF_2')))) | ~v1_funct_2(E_292, u1_struct_0(D_293), u1_struct_0('#skF_2')) | ~v1_funct_1(E_292) | ~m1_pre_topc(D_293, A_294) | v2_struct_0(D_293) | ~m1_pre_topc('#skF_3', A_294) | ~l1_pre_topc(A_294) | ~v2_pre_topc(A_294) | v2_struct_0(A_294))), inference(negUnitSimplification, [status(thm)], [c_62, c_56, c_297])).
% 5.15/1.94  tff(c_307, plain, (![A_294]: (r2_hidden('#skF_1'('#skF_4', '#skF_3', A_294, '#skF_3', '#skF_2', '#skF_4'), u1_struct_0('#skF_3')) | r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1(A_294, '#skF_2', '#skF_3', '#skF_3', '#skF_4'), '#skF_4') | ~m1_pre_topc('#skF_3', '#skF_3') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_3', A_294) | ~l1_pre_topc(A_294) | ~v2_pre_topc(A_294) | v2_struct_0(A_294))), inference(resolution, [status(thm)], [c_48, c_299])).
% 5.15/1.94  tff(c_318, plain, (![A_294]: (r2_hidden('#skF_1'('#skF_4', '#skF_3', A_294, '#skF_3', '#skF_2', '#skF_4'), u1_struct_0('#skF_3')) | r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1(A_294, '#skF_2', '#skF_3', '#skF_3', '#skF_4'), '#skF_4') | ~m1_pre_topc('#skF_3', '#skF_3') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_3', A_294) | ~l1_pre_topc(A_294) | ~v2_pre_topc(A_294) | v2_struct_0(A_294))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_307])).
% 5.15/1.94  tff(c_319, plain, (![A_294]: (r2_hidden('#skF_1'('#skF_4', '#skF_3', A_294, '#skF_3', '#skF_2', '#skF_4'), u1_struct_0('#skF_3')) | r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1(A_294, '#skF_2', '#skF_3', '#skF_3', '#skF_4'), '#skF_4') | ~m1_pre_topc('#skF_3', '#skF_3') | ~m1_pre_topc('#skF_3', A_294) | ~l1_pre_topc(A_294) | ~v2_pre_topc(A_294) | v2_struct_0(A_294))), inference(negUnitSimplification, [status(thm)], [c_56, c_318])).
% 5.15/1.94  tff(c_320, plain, (~m1_pre_topc('#skF_3', '#skF_3')), inference(splitLeft, [status(thm)], [c_319])).
% 5.15/1.94  tff(c_323, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_30, c_320])).
% 5.15/1.94  tff(c_327, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_75, c_323])).
% 5.15/1.94  tff(c_329, plain, (m1_pre_topc('#skF_3', '#skF_3')), inference(splitRight, [status(thm)], [c_319])).
% 5.15/1.94  tff(c_154, plain, (![D_242, A_243, C_239, E_240, B_241]: (v1_funct_1(k3_tmap_1(A_243, B_241, C_239, D_242, E_240)) | ~m1_subset_1(E_240, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_239), u1_struct_0(B_241)))) | ~v1_funct_2(E_240, u1_struct_0(C_239), u1_struct_0(B_241)) | ~v1_funct_1(E_240) | ~m1_pre_topc(D_242, A_243) | ~m1_pre_topc(C_239, A_243) | ~l1_pre_topc(B_241) | ~v2_pre_topc(B_241) | v2_struct_0(B_241) | ~l1_pre_topc(A_243) | ~v2_pre_topc(A_243) | v2_struct_0(A_243))), inference(cnfTransformation, [status(thm)], [f_125])).
% 5.15/1.94  tff(c_158, plain, (![A_243, D_242]: (v1_funct_1(k3_tmap_1(A_243, '#skF_2', '#skF_3', D_242, '#skF_4')) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~m1_pre_topc(D_242, A_243) | ~m1_pre_topc('#skF_3', A_243) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_243) | ~v2_pre_topc(A_243) | v2_struct_0(A_243))), inference(resolution, [status(thm)], [c_48, c_154])).
% 5.15/1.94  tff(c_162, plain, (![A_243, D_242]: (v1_funct_1(k3_tmap_1(A_243, '#skF_2', '#skF_3', D_242, '#skF_4')) | ~m1_pre_topc(D_242, A_243) | ~m1_pre_topc('#skF_3', A_243) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_243) | ~v2_pre_topc(A_243) | v2_struct_0(A_243))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_52, c_50, c_158])).
% 5.15/1.94  tff(c_163, plain, (![A_243, D_242]: (v1_funct_1(k3_tmap_1(A_243, '#skF_2', '#skF_3', D_242, '#skF_4')) | ~m1_pre_topc(D_242, A_243) | ~m1_pre_topc('#skF_3', A_243) | ~l1_pre_topc(A_243) | ~v2_pre_topc(A_243) | v2_struct_0(A_243))), inference(negUnitSimplification, [status(thm)], [c_62, c_162])).
% 5.15/1.94  tff(c_164, plain, (![C_244, E_245, D_247, A_248, B_246]: (v1_funct_2(k3_tmap_1(A_248, B_246, C_244, D_247, E_245), u1_struct_0(D_247), u1_struct_0(B_246)) | ~m1_subset_1(E_245, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_244), u1_struct_0(B_246)))) | ~v1_funct_2(E_245, u1_struct_0(C_244), u1_struct_0(B_246)) | ~v1_funct_1(E_245) | ~m1_pre_topc(D_247, A_248) | ~m1_pre_topc(C_244, A_248) | ~l1_pre_topc(B_246) | ~v2_pre_topc(B_246) | v2_struct_0(B_246) | ~l1_pre_topc(A_248) | ~v2_pre_topc(A_248) | v2_struct_0(A_248))), inference(cnfTransformation, [status(thm)], [f_125])).
% 5.15/1.94  tff(c_168, plain, (![A_248, D_247]: (v1_funct_2(k3_tmap_1(A_248, '#skF_2', '#skF_3', D_247, '#skF_4'), u1_struct_0(D_247), u1_struct_0('#skF_2')) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~m1_pre_topc(D_247, A_248) | ~m1_pre_topc('#skF_3', A_248) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_248) | ~v2_pre_topc(A_248) | v2_struct_0(A_248))), inference(resolution, [status(thm)], [c_48, c_164])).
% 5.15/1.94  tff(c_172, plain, (![A_248, D_247]: (v1_funct_2(k3_tmap_1(A_248, '#skF_2', '#skF_3', D_247, '#skF_4'), u1_struct_0(D_247), u1_struct_0('#skF_2')) | ~m1_pre_topc(D_247, A_248) | ~m1_pre_topc('#skF_3', A_248) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_248) | ~v2_pre_topc(A_248) | v2_struct_0(A_248))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_52, c_50, c_168])).
% 5.15/1.94  tff(c_173, plain, (![A_248, D_247]: (v1_funct_2(k3_tmap_1(A_248, '#skF_2', '#skF_3', D_247, '#skF_4'), u1_struct_0(D_247), u1_struct_0('#skF_2')) | ~m1_pre_topc(D_247, A_248) | ~m1_pre_topc('#skF_3', A_248) | ~l1_pre_topc(A_248) | ~v2_pre_topc(A_248) | v2_struct_0(A_248))), inference(negUnitSimplification, [status(thm)], [c_62, c_172])).
% 5.15/1.94  tff(c_18, plain, (![A_23, B_24, D_26, C_25, E_27]: (m1_subset_1(k3_tmap_1(A_23, B_24, C_25, D_26, E_27), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_26), u1_struct_0(B_24)))) | ~m1_subset_1(E_27, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_25), u1_struct_0(B_24)))) | ~v1_funct_2(E_27, u1_struct_0(C_25), u1_struct_0(B_24)) | ~v1_funct_1(E_27) | ~m1_pre_topc(D_26, A_23) | ~m1_pre_topc(C_25, A_23) | ~l1_pre_topc(B_24) | ~v2_pre_topc(B_24) | v2_struct_0(B_24) | ~l1_pre_topc(A_23) | ~v2_pre_topc(A_23) | v2_struct_0(A_23))), inference(cnfTransformation, [status(thm)], [f_125])).
% 5.15/1.94  tff(c_182, plain, (![C_261, B_262, D_263, A_264]: (r2_funct_2(u1_struct_0(C_261), u1_struct_0(B_262), D_263, k3_tmap_1(A_264, B_262, C_261, C_261, D_263)) | ~m1_subset_1(D_263, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_261), u1_struct_0(B_262)))) | ~v1_funct_2(D_263, u1_struct_0(C_261), u1_struct_0(B_262)) | ~v1_funct_1(D_263) | ~m1_pre_topc(C_261, A_264) | v2_struct_0(C_261) | ~l1_pre_topc(B_262) | ~v2_pre_topc(B_262) | v2_struct_0(B_262) | ~l1_pre_topc(A_264) | ~v2_pre_topc(A_264) | v2_struct_0(A_264))), inference(cnfTransformation, [status(thm)], [f_226])).
% 5.15/1.94  tff(c_186, plain, (![A_264]: (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', k3_tmap_1(A_264, '#skF_2', '#skF_3', '#skF_3', '#skF_4')) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~m1_pre_topc('#skF_3', A_264) | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_264) | ~v2_pre_topc(A_264) | v2_struct_0(A_264))), inference(resolution, [status(thm)], [c_48, c_182])).
% 5.15/1.94  tff(c_190, plain, (![A_264]: (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', k3_tmap_1(A_264, '#skF_2', '#skF_3', '#skF_3', '#skF_4')) | ~m1_pre_topc('#skF_3', A_264) | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_264) | ~v2_pre_topc(A_264) | v2_struct_0(A_264))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_52, c_50, c_186])).
% 5.15/1.94  tff(c_192, plain, (![A_265]: (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', k3_tmap_1(A_265, '#skF_2', '#skF_3', '#skF_3', '#skF_4')) | ~m1_pre_topc('#skF_3', A_265) | ~l1_pre_topc(A_265) | ~v2_pre_topc(A_265) | v2_struct_0(A_265))), inference(negUnitSimplification, [status(thm)], [c_62, c_56, c_190])).
% 5.15/1.94  tff(c_8, plain, (![D_10, C_9, A_7, B_8]: (D_10=C_9 | ~r2_funct_2(A_7, B_8, C_9, D_10) | ~m1_subset_1(D_10, k1_zfmisc_1(k2_zfmisc_1(A_7, B_8))) | ~v1_funct_2(D_10, A_7, B_8) | ~v1_funct_1(D_10) | ~m1_subset_1(C_9, k1_zfmisc_1(k2_zfmisc_1(A_7, B_8))) | ~v1_funct_2(C_9, A_7, B_8) | ~v1_funct_1(C_9))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.15/1.94  tff(c_194, plain, (![A_265]: (k3_tmap_1(A_265, '#skF_2', '#skF_3', '#skF_3', '#skF_4')='#skF_4' | ~m1_subset_1(k3_tmap_1(A_265, '#skF_2', '#skF_3', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k3_tmap_1(A_265, '#skF_2', '#skF_3', '#skF_3', '#skF_4'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1(A_265, '#skF_2', '#skF_3', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~m1_pre_topc('#skF_3', A_265) | ~l1_pre_topc(A_265) | ~v2_pre_topc(A_265) | v2_struct_0(A_265))), inference(resolution, [status(thm)], [c_192, c_8])).
% 5.15/1.94  tff(c_215, plain, (![A_275]: (k3_tmap_1(A_275, '#skF_2', '#skF_3', '#skF_3', '#skF_4')='#skF_4' | ~m1_subset_1(k3_tmap_1(A_275, '#skF_2', '#skF_3', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k3_tmap_1(A_275, '#skF_2', '#skF_3', '#skF_3', '#skF_4'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1(A_275, '#skF_2', '#skF_3', '#skF_3', '#skF_4')) | ~m1_pre_topc('#skF_3', A_275) | ~l1_pre_topc(A_275) | ~v2_pre_topc(A_275) | v2_struct_0(A_275))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_194])).
% 5.15/1.94  tff(c_219, plain, (![A_23]: (k3_tmap_1(A_23, '#skF_2', '#skF_3', '#skF_3', '#skF_4')='#skF_4' | ~v1_funct_2(k3_tmap_1(A_23, '#skF_2', '#skF_3', '#skF_3', '#skF_4'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1(A_23, '#skF_2', '#skF_3', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~m1_pre_topc('#skF_3', A_23) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_23) | ~v2_pre_topc(A_23) | v2_struct_0(A_23))), inference(resolution, [status(thm)], [c_18, c_215])).
% 5.15/1.94  tff(c_222, plain, (![A_23]: (k3_tmap_1(A_23, '#skF_2', '#skF_3', '#skF_3', '#skF_4')='#skF_4' | ~v1_funct_2(k3_tmap_1(A_23, '#skF_2', '#skF_3', '#skF_3', '#skF_4'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1(A_23, '#skF_2', '#skF_3', '#skF_3', '#skF_4')) | ~m1_pre_topc('#skF_3', A_23) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_23) | ~v2_pre_topc(A_23) | v2_struct_0(A_23))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_52, c_50, c_48, c_219])).
% 5.15/1.94  tff(c_224, plain, (![A_276]: (k3_tmap_1(A_276, '#skF_2', '#skF_3', '#skF_3', '#skF_4')='#skF_4' | ~v1_funct_2(k3_tmap_1(A_276, '#skF_2', '#skF_3', '#skF_3', '#skF_4'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1(A_276, '#skF_2', '#skF_3', '#skF_3', '#skF_4')) | ~m1_pre_topc('#skF_3', A_276) | ~l1_pre_topc(A_276) | ~v2_pre_topc(A_276) | v2_struct_0(A_276))), inference(negUnitSimplification, [status(thm)], [c_62, c_222])).
% 5.15/1.94  tff(c_230, plain, (![A_277]: (k3_tmap_1(A_277, '#skF_2', '#skF_3', '#skF_3', '#skF_4')='#skF_4' | ~v1_funct_1(k3_tmap_1(A_277, '#skF_2', '#skF_3', '#skF_3', '#skF_4')) | ~m1_pre_topc('#skF_3', A_277) | ~l1_pre_topc(A_277) | ~v2_pre_topc(A_277) | v2_struct_0(A_277))), inference(resolution, [status(thm)], [c_173, c_224])).
% 5.15/1.94  tff(c_236, plain, (![A_278]: (k3_tmap_1(A_278, '#skF_2', '#skF_3', '#skF_3', '#skF_4')='#skF_4' | ~m1_pre_topc('#skF_3', A_278) | ~l1_pre_topc(A_278) | ~v2_pre_topc(A_278) | v2_struct_0(A_278))), inference(resolution, [status(thm)], [c_163, c_230])).
% 5.15/1.94  tff(c_243, plain, (k3_tmap_1('#skF_2', '#skF_2', '#skF_3', '#skF_3', '#skF_4')='#skF_4' | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_54, c_236])).
% 5.15/1.94  tff(c_250, plain, (k3_tmap_1('#skF_2', '#skF_2', '#skF_3', '#skF_3', '#skF_4')='#skF_4' | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_243])).
% 5.15/1.94  tff(c_251, plain, (k3_tmap_1('#skF_2', '#skF_2', '#skF_3', '#skF_3', '#skF_4')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_62, c_250])).
% 5.15/1.94  tff(c_403, plain, (![F_319, C_317, D_315, B_318, E_314, A_316]: (m1_subset_1('#skF_1'(E_314, D_315, A_316, C_317, B_318, F_319), u1_struct_0(D_315)) | r2_funct_2(u1_struct_0(C_317), u1_struct_0(B_318), k3_tmap_1(A_316, B_318, D_315, C_317, E_314), F_319) | ~m1_subset_1(F_319, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_317), u1_struct_0(B_318)))) | ~v1_funct_2(F_319, u1_struct_0(C_317), u1_struct_0(B_318)) | ~v1_funct_1(F_319) | ~m1_pre_topc(C_317, D_315) | ~m1_subset_1(E_314, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_315), u1_struct_0(B_318)))) | ~v1_funct_2(E_314, u1_struct_0(D_315), u1_struct_0(B_318)) | ~v1_funct_1(E_314) | ~m1_pre_topc(D_315, A_316) | v2_struct_0(D_315) | ~m1_pre_topc(C_317, A_316) | v2_struct_0(C_317) | ~l1_pre_topc(B_318) | ~v2_pre_topc(B_318) | v2_struct_0(B_318) | ~l1_pre_topc(A_316) | ~v2_pre_topc(A_316) | v2_struct_0(A_316))), inference(cnfTransformation, [status(thm)], [f_196])).
% 5.15/1.94  tff(c_567, plain, (![B_381, A_379, E_380, D_378, A_382]: (m1_subset_1('#skF_1'(E_380, D_378, A_382, B_381, A_379, k4_tmap_1(A_379, B_381)), u1_struct_0(D_378)) | r2_funct_2(u1_struct_0(B_381), u1_struct_0(A_379), k3_tmap_1(A_382, A_379, D_378, B_381, E_380), k4_tmap_1(A_379, B_381)) | ~v1_funct_2(k4_tmap_1(A_379, B_381), u1_struct_0(B_381), u1_struct_0(A_379)) | ~v1_funct_1(k4_tmap_1(A_379, B_381)) | ~m1_pre_topc(B_381, D_378) | ~m1_subset_1(E_380, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_378), u1_struct_0(A_379)))) | ~v1_funct_2(E_380, u1_struct_0(D_378), u1_struct_0(A_379)) | ~v1_funct_1(E_380) | ~m1_pre_topc(D_378, A_382) | v2_struct_0(D_378) | ~m1_pre_topc(B_381, A_382) | v2_struct_0(B_381) | ~l1_pre_topc(A_382) | ~v2_pre_topc(A_382) | v2_struct_0(A_382) | ~m1_pre_topc(B_381, A_379) | ~l1_pre_topc(A_379) | ~v2_pre_topc(A_379) | v2_struct_0(A_379))), inference(resolution, [status(thm)], [c_24, c_403])).
% 5.15/1.94  tff(c_580, plain, (m1_subset_1('#skF_1'('#skF_4', '#skF_3', '#skF_2', '#skF_3', '#skF_2', k4_tmap_1('#skF_2', '#skF_3')), u1_struct_0('#skF_3')) | r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', k4_tmap_1('#skF_2', '#skF_3')) | ~v1_funct_2(k4_tmap_1('#skF_2', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k4_tmap_1('#skF_2', '#skF_3')) | ~m1_pre_topc('#skF_3', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_2') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_3', '#skF_2') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_251, c_567])).
% 5.15/1.94  tff(c_586, plain, (m1_subset_1('#skF_1'('#skF_4', '#skF_3', '#skF_2', '#skF_3', '#skF_2', k4_tmap_1('#skF_2', '#skF_3')), u1_struct_0('#skF_3')) | r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', k4_tmap_1('#skF_2', '#skF_3')) | ~v1_funct_2(k4_tmap_1('#skF_2', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k4_tmap_1('#skF_2', '#skF_3')) | v2_struct_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_54, c_60, c_58, c_54, c_54, c_52, c_50, c_48, c_329, c_580])).
% 5.15/1.94  tff(c_587, plain, (m1_subset_1('#skF_1'('#skF_4', '#skF_3', '#skF_2', '#skF_3', '#skF_2', k4_tmap_1('#skF_2', '#skF_3')), u1_struct_0('#skF_3')) | r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', k4_tmap_1('#skF_2', '#skF_3')) | ~v1_funct_2(k4_tmap_1('#skF_2', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k4_tmap_1('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_62, c_56, c_586])).
% 5.15/1.94  tff(c_588, plain, (~v1_funct_1(k4_tmap_1('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_587])).
% 5.15/1.94  tff(c_591, plain, (~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_28, c_588])).
% 5.15/1.94  tff(c_594, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_54, c_591])).
% 5.15/1.94  tff(c_596, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_594])).
% 5.15/1.94  tff(c_598, plain, (v1_funct_1(k4_tmap_1('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_587])).
% 5.15/1.94  tff(c_26, plain, (![A_28, B_29]: (v1_funct_2(k4_tmap_1(A_28, B_29), u1_struct_0(B_29), u1_struct_0(A_28)) | ~m1_pre_topc(B_29, A_28) | ~l1_pre_topc(A_28) | ~v2_pre_topc(A_28) | v2_struct_0(A_28))), inference(cnfTransformation, [status(thm)], [f_140])).
% 5.15/1.94  tff(c_597, plain, (~v1_funct_2(k4_tmap_1('#skF_2', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', k4_tmap_1('#skF_2', '#skF_3')) | m1_subset_1('#skF_1'('#skF_4', '#skF_3', '#skF_2', '#skF_3', '#skF_2', k4_tmap_1('#skF_2', '#skF_3')), u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_587])).
% 5.15/1.94  tff(c_599, plain, (~v1_funct_2(k4_tmap_1('#skF_2', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_597])).
% 5.15/1.94  tff(c_612, plain, (~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_26, c_599])).
% 5.15/1.94  tff(c_615, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_54, c_612])).
% 5.15/1.94  tff(c_617, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_615])).
% 5.15/1.94  tff(c_619, plain, (v1_funct_2(k4_tmap_1('#skF_2', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_597])).
% 5.15/1.94  tff(c_618, plain, (m1_subset_1('#skF_1'('#skF_4', '#skF_3', '#skF_2', '#skF_3', '#skF_2', k4_tmap_1('#skF_2', '#skF_3')), u1_struct_0('#skF_3')) | r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', k4_tmap_1('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_597])).
% 5.15/1.94  tff(c_620, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', k4_tmap_1('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_618])).
% 5.15/1.94  tff(c_635, plain, (k4_tmap_1('#skF_2', '#skF_3')='#skF_4' | ~m1_subset_1(k4_tmap_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k4_tmap_1('#skF_2', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k4_tmap_1('#skF_2', '#skF_3')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_620, c_8])).
% 5.15/1.94  tff(c_638, plain, (k4_tmap_1('#skF_2', '#skF_3')='#skF_4' | ~m1_subset_1(k4_tmap_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_598, c_619, c_635])).
% 5.15/1.94  tff(c_639, plain, (~m1_subset_1(k4_tmap_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(splitLeft, [status(thm)], [c_638])).
% 5.15/1.94  tff(c_642, plain, (~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_24, c_639])).
% 5.15/1.94  tff(c_645, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_54, c_642])).
% 5.15/1.94  tff(c_647, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_645])).
% 5.15/1.94  tff(c_648, plain, (k4_tmap_1('#skF_2', '#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_638])).
% 5.15/1.94  tff(c_44, plain, (~r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k4_tmap_1('#skF_2', '#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_288])).
% 5.15/1.94  tff(c_653, plain, (~r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_648, c_44])).
% 5.15/1.94  tff(c_659, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_124, c_653])).
% 5.15/1.94  tff(c_661, plain, (~r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', k4_tmap_1('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_618])).
% 5.15/1.94  tff(c_660, plain, (m1_subset_1('#skF_1'('#skF_4', '#skF_3', '#skF_2', '#skF_3', '#skF_2', k4_tmap_1('#skF_2', '#skF_3')), u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_618])).
% 5.15/1.94  tff(c_16, plain, (![C_22, A_16, B_20]: (m1_subset_1(C_22, u1_struct_0(A_16)) | ~m1_subset_1(C_22, u1_struct_0(B_20)) | ~m1_pre_topc(B_20, A_16) | v2_struct_0(B_20) | ~l1_pre_topc(A_16) | v2_struct_0(A_16))), inference(cnfTransformation, [status(thm)], [f_95])).
% 5.15/1.94  tff(c_677, plain, (![A_16]: (m1_subset_1('#skF_1'('#skF_4', '#skF_3', '#skF_2', '#skF_3', '#skF_2', k4_tmap_1('#skF_2', '#skF_3')), u1_struct_0(A_16)) | ~m1_pre_topc('#skF_3', A_16) | v2_struct_0('#skF_3') | ~l1_pre_topc(A_16) | v2_struct_0(A_16))), inference(resolution, [status(thm)], [c_660, c_16])).
% 5.15/1.94  tff(c_697, plain, (![A_397]: (m1_subset_1('#skF_1'('#skF_4', '#skF_3', '#skF_2', '#skF_3', '#skF_2', k4_tmap_1('#skF_2', '#skF_3')), u1_struct_0(A_397)) | ~m1_pre_topc('#skF_3', A_397) | ~l1_pre_topc(A_397) | v2_struct_0(A_397))), inference(negUnitSimplification, [status(thm)], [c_56, c_677])).
% 5.15/1.94  tff(c_114, plain, (![A_1]: (k1_funct_1('#skF_4', A_1)=A_1 | ~m1_subset_1(A_1, u1_struct_0('#skF_2')) | ~m1_subset_1(A_1, u1_struct_0('#skF_3')))), inference(splitRight, [status(thm)], [c_83])).
% 5.15/1.94  tff(c_707, plain, (k1_funct_1('#skF_4', '#skF_1'('#skF_4', '#skF_3', '#skF_2', '#skF_3', '#skF_2', k4_tmap_1('#skF_2', '#skF_3')))='#skF_1'('#skF_4', '#skF_3', '#skF_2', '#skF_3', '#skF_2', k4_tmap_1('#skF_2', '#skF_3')) | ~m1_subset_1('#skF_1'('#skF_4', '#skF_3', '#skF_2', '#skF_3', '#skF_2', k4_tmap_1('#skF_2', '#skF_3')), u1_struct_0('#skF_3')) | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_697, c_114])).
% 5.15/1.94  tff(c_713, plain, (k1_funct_1('#skF_4', '#skF_1'('#skF_4', '#skF_3', '#skF_2', '#skF_3', '#skF_2', k4_tmap_1('#skF_2', '#skF_3')))='#skF_1'('#skF_4', '#skF_3', '#skF_2', '#skF_3', '#skF_2', k4_tmap_1('#skF_2', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_54, c_660, c_707])).
% 5.15/1.94  tff(c_714, plain, (k1_funct_1('#skF_4', '#skF_1'('#skF_4', '#skF_3', '#skF_2', '#skF_3', '#skF_2', k4_tmap_1('#skF_2', '#skF_3')))='#skF_1'('#skF_4', '#skF_3', '#skF_2', '#skF_3', '#skF_2', k4_tmap_1('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_62, c_713])).
% 5.15/1.94  tff(c_4, plain, (![A_3, B_4, C_5, D_6]: (k3_funct_2(A_3, B_4, C_5, D_6)=k1_funct_1(C_5, D_6) | ~m1_subset_1(D_6, A_3) | ~m1_subset_1(C_5, k1_zfmisc_1(k2_zfmisc_1(A_3, B_4))) | ~v1_funct_2(C_5, A_3, B_4) | ~v1_funct_1(C_5) | v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.15/1.94  tff(c_675, plain, (![B_4, C_5]: (k3_funct_2(u1_struct_0('#skF_3'), B_4, C_5, '#skF_1'('#skF_4', '#skF_3', '#skF_2', '#skF_3', '#skF_2', k4_tmap_1('#skF_2', '#skF_3')))=k1_funct_1(C_5, '#skF_1'('#skF_4', '#skF_3', '#skF_2', '#skF_3', '#skF_2', k4_tmap_1('#skF_2', '#skF_3'))) | ~m1_subset_1(C_5, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), B_4))) | ~v1_funct_2(C_5, u1_struct_0('#skF_3'), B_4) | ~v1_funct_1(C_5) | v1_xboole_0(u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_660, c_4])).
% 5.15/1.94  tff(c_807, plain, (![B_409, C_410]: (k3_funct_2(u1_struct_0('#skF_3'), B_409, C_410, '#skF_1'('#skF_4', '#skF_3', '#skF_2', '#skF_3', '#skF_2', k4_tmap_1('#skF_2', '#skF_3')))=k1_funct_1(C_410, '#skF_1'('#skF_4', '#skF_3', '#skF_2', '#skF_3', '#skF_2', k4_tmap_1('#skF_2', '#skF_3'))) | ~m1_subset_1(C_410, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), B_409))) | ~v1_funct_2(C_410, u1_struct_0('#skF_3'), B_409) | ~v1_funct_1(C_410))), inference(negUnitSimplification, [status(thm)], [c_115, c_675])).
% 5.15/1.94  tff(c_818, plain, (k3_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', '#skF_1'('#skF_4', '#skF_3', '#skF_2', '#skF_3', '#skF_2', k4_tmap_1('#skF_2', '#skF_3')))=k1_funct_1('#skF_4', '#skF_1'('#skF_4', '#skF_3', '#skF_2', '#skF_3', '#skF_2', k4_tmap_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_48, c_807])).
% 5.15/1.94  tff(c_823, plain, (k3_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', '#skF_1'('#skF_4', '#skF_3', '#skF_2', '#skF_3', '#skF_2', k4_tmap_1('#skF_2', '#skF_3')))='#skF_1'('#skF_4', '#skF_3', '#skF_2', '#skF_3', '#skF_2', k4_tmap_1('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_714, c_818])).
% 5.15/1.94  tff(c_32, plain, (![E_151, A_31, B_95, F_155, D_143, C_127]: (k3_funct_2(u1_struct_0(D_143), u1_struct_0(B_95), E_151, '#skF_1'(E_151, D_143, A_31, C_127, B_95, F_155))!=k1_funct_1(F_155, '#skF_1'(E_151, D_143, A_31, C_127, B_95, F_155)) | r2_funct_2(u1_struct_0(C_127), u1_struct_0(B_95), k3_tmap_1(A_31, B_95, D_143, C_127, E_151), F_155) | ~m1_subset_1(F_155, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_127), u1_struct_0(B_95)))) | ~v1_funct_2(F_155, u1_struct_0(C_127), u1_struct_0(B_95)) | ~v1_funct_1(F_155) | ~m1_pre_topc(C_127, D_143) | ~m1_subset_1(E_151, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_143), u1_struct_0(B_95)))) | ~v1_funct_2(E_151, u1_struct_0(D_143), u1_struct_0(B_95)) | ~v1_funct_1(E_151) | ~m1_pre_topc(D_143, A_31) | v2_struct_0(D_143) | ~m1_pre_topc(C_127, A_31) | v2_struct_0(C_127) | ~l1_pre_topc(B_95) | ~v2_pre_topc(B_95) | v2_struct_0(B_95) | ~l1_pre_topc(A_31) | ~v2_pre_topc(A_31) | v2_struct_0(A_31))), inference(cnfTransformation, [status(thm)], [f_196])).
% 5.15/1.94  tff(c_826, plain, (k1_funct_1(k4_tmap_1('#skF_2', '#skF_3'), '#skF_1'('#skF_4', '#skF_3', '#skF_2', '#skF_3', '#skF_2', k4_tmap_1('#skF_2', '#skF_3')))!='#skF_1'('#skF_4', '#skF_3', '#skF_2', '#skF_3', '#skF_2', k4_tmap_1('#skF_2', '#skF_3')) | r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_2', '#skF_2', '#skF_3', '#skF_3', '#skF_4'), k4_tmap_1('#skF_2', '#skF_3')) | ~m1_subset_1(k4_tmap_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k4_tmap_1('#skF_2', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k4_tmap_1('#skF_2', '#skF_3')) | ~m1_pre_topc('#skF_3', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_2') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_3', '#skF_2') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_823, c_32])).
% 5.15/1.94  tff(c_830, plain, (k1_funct_1(k4_tmap_1('#skF_2', '#skF_3'), '#skF_1'('#skF_4', '#skF_3', '#skF_2', '#skF_3', '#skF_2', k4_tmap_1('#skF_2', '#skF_3')))!='#skF_1'('#skF_4', '#skF_3', '#skF_2', '#skF_3', '#skF_2', k4_tmap_1('#skF_2', '#skF_3')) | r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', k4_tmap_1('#skF_2', '#skF_3')) | ~m1_subset_1(k4_tmap_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | v2_struct_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_60, c_58, c_54, c_54, c_52, c_50, c_48, c_329, c_598, c_619, c_251, c_826])).
% 5.15/1.94  tff(c_831, plain, (k1_funct_1(k4_tmap_1('#skF_2', '#skF_3'), '#skF_1'('#skF_4', '#skF_3', '#skF_2', '#skF_3', '#skF_2', k4_tmap_1('#skF_2', '#skF_3')))!='#skF_1'('#skF_4', '#skF_3', '#skF_2', '#skF_3', '#skF_2', k4_tmap_1('#skF_2', '#skF_3')) | ~m1_subset_1(k4_tmap_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_62, c_56, c_661, c_830])).
% 5.15/1.94  tff(c_833, plain, (~m1_subset_1(k4_tmap_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(splitLeft, [status(thm)], [c_831])).
% 5.15/1.94  tff(c_860, plain, (~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_24, c_833])).
% 5.15/1.94  tff(c_863, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_54, c_860])).
% 5.15/1.94  tff(c_865, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_863])).
% 5.15/1.94  tff(c_866, plain, (k1_funct_1(k4_tmap_1('#skF_2', '#skF_3'), '#skF_1'('#skF_4', '#skF_3', '#skF_2', '#skF_3', '#skF_2', k4_tmap_1('#skF_2', '#skF_3')))!='#skF_1'('#skF_4', '#skF_3', '#skF_2', '#skF_3', '#skF_2', k4_tmap_1('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_831])).
% 5.15/1.94  tff(c_719, plain, (![A_398, A_399]: (m1_subset_1('#skF_1'('#skF_4', '#skF_3', '#skF_2', '#skF_3', '#skF_2', k4_tmap_1('#skF_2', '#skF_3')), u1_struct_0(A_398)) | ~m1_pre_topc(A_399, A_398) | ~l1_pre_topc(A_398) | v2_struct_0(A_398) | ~m1_pre_topc('#skF_3', A_399) | ~l1_pre_topc(A_399) | v2_struct_0(A_399))), inference(resolution, [status(thm)], [c_697, c_16])).
% 5.15/1.94  tff(c_725, plain, (m1_subset_1('#skF_1'('#skF_4', '#skF_3', '#skF_2', '#skF_3', '#skF_2', k4_tmap_1('#skF_2', '#skF_3')), u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~m1_pre_topc('#skF_3', '#skF_3') | ~l1_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_54, c_719])).
% 5.15/1.94  tff(c_733, plain, (m1_subset_1('#skF_1'('#skF_4', '#skF_3', '#skF_2', '#skF_3', '#skF_2', k4_tmap_1('#skF_2', '#skF_3')), u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_75, c_329, c_58, c_725])).
% 5.15/1.94  tff(c_734, plain, (m1_subset_1('#skF_1'('#skF_4', '#skF_3', '#skF_2', '#skF_3', '#skF_2', k4_tmap_1('#skF_2', '#skF_3')), u1_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_56, c_62, c_733])).
% 5.15/1.94  tff(c_129, plain, (![A_223, B_224, C_225]: (k1_funct_1(k4_tmap_1(A_223, B_224), C_225)=C_225 | ~r2_hidden(C_225, u1_struct_0(B_224)) | ~m1_subset_1(C_225, u1_struct_0(A_223)) | ~m1_pre_topc(B_224, A_223) | v2_struct_0(B_224) | ~l1_pre_topc(A_223) | ~v2_pre_topc(A_223) | v2_struct_0(A_223))), inference(cnfTransformation, [status(thm)], [f_258])).
% 5.15/1.94  tff(c_133, plain, (![A_223, B_224, A_1]: (k1_funct_1(k4_tmap_1(A_223, B_224), A_1)=A_1 | ~m1_subset_1(A_1, u1_struct_0(A_223)) | ~m1_pre_topc(B_224, A_223) | v2_struct_0(B_224) | ~l1_pre_topc(A_223) | ~v2_pre_topc(A_223) | v2_struct_0(A_223) | v1_xboole_0(u1_struct_0(B_224)) | ~m1_subset_1(A_1, u1_struct_0(B_224)))), inference(resolution, [status(thm)], [c_2, c_129])).
% 5.15/1.94  tff(c_736, plain, (![B_224]: (k1_funct_1(k4_tmap_1('#skF_2', B_224), '#skF_1'('#skF_4', '#skF_3', '#skF_2', '#skF_3', '#skF_2', k4_tmap_1('#skF_2', '#skF_3')))='#skF_1'('#skF_4', '#skF_3', '#skF_2', '#skF_3', '#skF_2', k4_tmap_1('#skF_2', '#skF_3')) | ~m1_pre_topc(B_224, '#skF_2') | v2_struct_0(B_224) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | v1_xboole_0(u1_struct_0(B_224)) | ~m1_subset_1('#skF_1'('#skF_4', '#skF_3', '#skF_2', '#skF_3', '#skF_2', k4_tmap_1('#skF_2', '#skF_3')), u1_struct_0(B_224)))), inference(resolution, [status(thm)], [c_734, c_133])).
% 5.15/1.94  tff(c_746, plain, (![B_224]: (k1_funct_1(k4_tmap_1('#skF_2', B_224), '#skF_1'('#skF_4', '#skF_3', '#skF_2', '#skF_3', '#skF_2', k4_tmap_1('#skF_2', '#skF_3')))='#skF_1'('#skF_4', '#skF_3', '#skF_2', '#skF_3', '#skF_2', k4_tmap_1('#skF_2', '#skF_3')) | ~m1_pre_topc(B_224, '#skF_2') | v2_struct_0(B_224) | v2_struct_0('#skF_2') | v1_xboole_0(u1_struct_0(B_224)) | ~m1_subset_1('#skF_1'('#skF_4', '#skF_3', '#skF_2', '#skF_3', '#skF_2', k4_tmap_1('#skF_2', '#skF_3')), u1_struct_0(B_224)))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_736])).
% 5.15/1.94  tff(c_1005, plain, (![B_436]: (k1_funct_1(k4_tmap_1('#skF_2', B_436), '#skF_1'('#skF_4', '#skF_3', '#skF_2', '#skF_3', '#skF_2', k4_tmap_1('#skF_2', '#skF_3')))='#skF_1'('#skF_4', '#skF_3', '#skF_2', '#skF_3', '#skF_2', k4_tmap_1('#skF_2', '#skF_3')) | ~m1_pre_topc(B_436, '#skF_2') | v2_struct_0(B_436) | v1_xboole_0(u1_struct_0(B_436)) | ~m1_subset_1('#skF_1'('#skF_4', '#skF_3', '#skF_2', '#skF_3', '#skF_2', k4_tmap_1('#skF_2', '#skF_3')), u1_struct_0(B_436)))), inference(negUnitSimplification, [status(thm)], [c_62, c_746])).
% 5.15/1.94  tff(c_1017, plain, (k1_funct_1(k4_tmap_1('#skF_2', '#skF_3'), '#skF_1'('#skF_4', '#skF_3', '#skF_2', '#skF_3', '#skF_2', k4_tmap_1('#skF_2', '#skF_3')))='#skF_1'('#skF_4', '#skF_3', '#skF_2', '#skF_3', '#skF_2', k4_tmap_1('#skF_2', '#skF_3')) | ~m1_pre_topc('#skF_3', '#skF_2') | v2_struct_0('#skF_3') | v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_660, c_1005])).
% 5.15/1.94  tff(c_1027, plain, (k1_funct_1(k4_tmap_1('#skF_2', '#skF_3'), '#skF_1'('#skF_4', '#skF_3', '#skF_2', '#skF_3', '#skF_2', k4_tmap_1('#skF_2', '#skF_3')))='#skF_1'('#skF_4', '#skF_3', '#skF_2', '#skF_3', '#skF_2', k4_tmap_1('#skF_2', '#skF_3')) | v2_struct_0('#skF_3') | v1_xboole_0(u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_1017])).
% 5.15/1.94  tff(c_1029, plain, $false, inference(negUnitSimplification, [status(thm)], [c_115, c_56, c_866, c_1027])).
% 5.15/1.94  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.15/1.94  
% 5.15/1.94  Inference rules
% 5.15/1.94  ----------------------
% 5.15/1.94  #Ref     : 0
% 5.15/1.94  #Sup     : 175
% 5.15/1.94  #Fact    : 0
% 5.15/1.94  #Define  : 0
% 5.15/1.94  #Split   : 10
% 5.15/1.94  #Chain   : 0
% 5.15/1.94  #Close   : 0
% 5.15/1.94  
% 5.15/1.94  Ordering : KBO
% 5.15/1.94  
% 5.15/1.94  Simplification rules
% 5.15/1.94  ----------------------
% 5.15/1.94  #Subsume      : 21
% 5.15/1.94  #Demod        : 423
% 5.15/1.94  #Tautology    : 35
% 5.15/1.94  #SimpNegUnit  : 70
% 5.15/1.94  #BackRed      : 4
% 5.15/1.94  
% 5.15/1.94  #Partial instantiations: 0
% 5.15/1.94  #Strategies tried      : 1
% 5.15/1.94  
% 5.15/1.94  Timing (in seconds)
% 5.15/1.94  ----------------------
% 5.15/1.94  Preprocessing        : 0.42
% 5.15/1.94  Parsing              : 0.22
% 5.15/1.94  CNF conversion       : 0.04
% 5.15/1.94  Main loop            : 0.67
% 5.15/1.94  Inferencing          : 0.25
% 5.15/1.94  Reduction            : 0.18
% 5.15/1.94  Demodulation         : 0.13
% 5.15/1.94  BG Simplification    : 0.04
% 5.15/1.94  Subsumption          : 0.17
% 5.15/1.94  Abstraction          : 0.03
% 5.15/1.94  MUC search           : 0.00
% 5.15/1.94  Cooper               : 0.00
% 5.15/1.94  Total                : 1.16
% 5.15/1.94  Index Insertion      : 0.00
% 5.15/1.95  Index Deletion       : 0.00
% 5.15/1.95  Index Matching       : 0.00
% 5.15/1.95  BG Taut test         : 0.00
%------------------------------------------------------------------------------
