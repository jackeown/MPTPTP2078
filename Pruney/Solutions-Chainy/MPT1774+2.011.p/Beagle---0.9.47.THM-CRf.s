%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:25 EST 2020

% Result     : Theorem 5.05s
% Output     : CNFRefutation 5.05s
% Verified   : 
% Statistics : Number of formulae       :  154 ( 537 expanded)
%              Number of leaves         :   37 ( 217 expanded)
%              Depth                    :   17
%              Number of atoms          :  555 (4485 expanded)
%              Number of equality atoms :   32 ( 194 expanded)
%              Maximal formula depth    :   26 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k3_tmap_1,type,(
    k3_tmap_1: ( $i * $i * $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_tmap_1,type,(
    r1_tmap_1: ( $i * $i * $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff('#skF_8',type,(
    '#skF_8': $i )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_250,negated_conjecture,(
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
                    ( ( ~ v2_struct_0(D)
                      & m1_pre_topc(D,B) )
                   => ! [E] :
                        ( ( v1_funct_1(E)
                          & v1_funct_2(E,u1_struct_0(D),u1_struct_0(A))
                          & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D),u1_struct_0(A)))) )
                       => ( m1_pre_topc(C,D)
                         => ! [F] :
                              ( m1_subset_1(F,k1_zfmisc_1(u1_struct_0(B)))
                             => ! [G] :
                                  ( m1_subset_1(G,u1_struct_0(D))
                                 => ! [H] :
                                      ( m1_subset_1(H,u1_struct_0(C))
                                     => ( ( v3_pre_topc(F,B)
                                          & r2_hidden(G,F)
                                          & r1_tarski(F,u1_struct_0(C))
                                          & G = H )
                                       => ( r1_tmap_1(D,A,E,G)
                                        <=> r1_tmap_1(C,A,k3_tmap_1(B,A,D,C,E),H) ) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_tmap_1)).

tff(f_45,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_55,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B)))
             => m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_pre_topc)).

tff(f_38,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_131,axiom,(
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

tff(f_99,axiom,(
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

tff(f_180,axiom,(
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
                & v1_funct_2(C,u1_struct_0(B),u1_struct_0(A))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B),u1_struct_0(A)))) )
             => ! [D] :
                  ( ( ~ v2_struct_0(D)
                    & m1_pre_topc(D,B) )
                 => ! [E] :
                      ( m1_subset_1(E,k1_zfmisc_1(u1_struct_0(B)))
                     => ! [F] :
                          ( m1_subset_1(F,u1_struct_0(B))
                         => ! [G] :
                              ( m1_subset_1(G,u1_struct_0(D))
                             => ( ( v3_pre_topc(E,B)
                                  & r2_hidden(F,E)
                                  & r1_tarski(E,u1_struct_0(D))
                                  & F = G )
                               => ( r1_tmap_1(B,A,C,F)
                                <=> r1_tmap_1(D,A,k2_tmap_1(B,A,C,D),G) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_tmap_1)).

tff(f_72,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_pre_topc(C,A)
             => ( v3_pre_topc(B,A)
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(C)))
                   => ( D = B
                     => v3_pre_topc(D,C) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_tops_2)).

tff(c_24,plain,(
    '#skF_7' = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_250])).

tff(c_34,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_250])).

tff(c_75,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_34])).

tff(c_32,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_250])).

tff(c_28,plain,(
    r2_hidden('#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_250])).

tff(c_76,plain,(
    r2_hidden('#skF_8','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_28])).

tff(c_26,plain,(
    r1_tarski('#skF_6',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_250])).

tff(c_54,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_250])).

tff(c_46,plain,(
    m1_pre_topc('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_250])).

tff(c_86,plain,(
    ! [B_460,A_461] :
      ( l1_pre_topc(B_460)
      | ~ m1_pre_topc(B_460,A_461)
      | ~ l1_pre_topc(A_461) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_92,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_86])).

tff(c_101,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_92])).

tff(c_38,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_250])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(A_1,k1_zfmisc_1(B_2))
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_164,plain,(
    ! [C_472,A_473,B_474] :
      ( m1_subset_1(C_472,k1_zfmisc_1(u1_struct_0(A_473)))
      | ~ m1_subset_1(C_472,k1_zfmisc_1(u1_struct_0(B_474)))
      | ~ m1_pre_topc(B_474,A_473)
      | ~ l1_pre_topc(A_473) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_181,plain,(
    ! [A_477,A_478,B_479] :
      ( m1_subset_1(A_477,k1_zfmisc_1(u1_struct_0(A_478)))
      | ~ m1_pre_topc(B_479,A_478)
      | ~ l1_pre_topc(A_478)
      | ~ r1_tarski(A_477,u1_struct_0(B_479)) ) ),
    inference(resolution,[status(thm)],[c_4,c_164])).

tff(c_189,plain,(
    ! [A_477] :
      ( m1_subset_1(A_477,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4')
      | ~ r1_tarski(A_477,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_38,c_181])).

tff(c_199,plain,(
    ! [A_477] :
      ( m1_subset_1(A_477,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_tarski(A_477,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_189])).

tff(c_64,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_250])).

tff(c_48,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_250])).

tff(c_52,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_250])).

tff(c_72,plain,
    ( r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_7')
    | r1_tmap_1('#skF_3','#skF_1',k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_250])).

tff(c_73,plain,
    ( r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_8')
    | r1_tmap_1('#skF_3','#skF_1',k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_72])).

tff(c_114,plain,(
    r1_tmap_1('#skF_3','#skF_1',k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5'),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_73])).

tff(c_66,plain,
    ( ~ r1_tmap_1('#skF_3','#skF_1',k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5'),'#skF_8')
    | ~ r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_250])).

tff(c_74,plain,
    ( ~ r1_tmap_1('#skF_3','#skF_1',k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5'),'#skF_8')
    | ~ r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_66])).

tff(c_163,plain,(
    ~ r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_74])).

tff(c_62,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_250])).

tff(c_60,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_250])).

tff(c_56,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_250])).

tff(c_115,plain,(
    ! [B_464,A_465] :
      ( v2_pre_topc(B_464)
      | ~ m1_pre_topc(B_464,A_465)
      | ~ l1_pre_topc(A_465)
      | ~ v2_pre_topc(A_465) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_121,plain,
    ( v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_115])).

tff(c_130,plain,(
    v2_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_121])).

tff(c_44,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_250])).

tff(c_42,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_250])).

tff(c_40,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_250])).

tff(c_58,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_250])).

tff(c_50,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_250])).

tff(c_391,plain,(
    ! [D_511,B_510,E_512,C_509,A_513] :
      ( k3_tmap_1(A_513,B_510,C_509,D_511,E_512) = k2_partfun1(u1_struct_0(C_509),u1_struct_0(B_510),E_512,u1_struct_0(D_511))
      | ~ m1_pre_topc(D_511,C_509)
      | ~ m1_subset_1(E_512,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_509),u1_struct_0(B_510))))
      | ~ v1_funct_2(E_512,u1_struct_0(C_509),u1_struct_0(B_510))
      | ~ v1_funct_1(E_512)
      | ~ m1_pre_topc(D_511,A_513)
      | ~ m1_pre_topc(C_509,A_513)
      | ~ l1_pre_topc(B_510)
      | ~ v2_pre_topc(B_510)
      | v2_struct_0(B_510)
      | ~ l1_pre_topc(A_513)
      | ~ v2_pre_topc(A_513)
      | v2_struct_0(A_513) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_393,plain,(
    ! [A_513,D_511] :
      ( k3_tmap_1(A_513,'#skF_1','#skF_4',D_511,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0(D_511))
      | ~ m1_pre_topc(D_511,'#skF_4')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_511,A_513)
      | ~ m1_pre_topc('#skF_4',A_513)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1')
      | ~ l1_pre_topc(A_513)
      | ~ v2_pre_topc(A_513)
      | v2_struct_0(A_513) ) ),
    inference(resolution,[status(thm)],[c_40,c_391])).

tff(c_399,plain,(
    ! [A_513,D_511] :
      ( k3_tmap_1(A_513,'#skF_1','#skF_4',D_511,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0(D_511))
      | ~ m1_pre_topc(D_511,'#skF_4')
      | ~ m1_pre_topc(D_511,A_513)
      | ~ m1_pre_topc('#skF_4',A_513)
      | v2_struct_0('#skF_1')
      | ~ l1_pre_topc(A_513)
      | ~ v2_pre_topc(A_513)
      | v2_struct_0(A_513) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_44,c_42,c_393])).

tff(c_402,plain,(
    ! [A_514,D_515] :
      ( k3_tmap_1(A_514,'#skF_1','#skF_4',D_515,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0(D_515))
      | ~ m1_pre_topc(D_515,'#skF_4')
      | ~ m1_pre_topc(D_515,A_514)
      | ~ m1_pre_topc('#skF_4',A_514)
      | ~ l1_pre_topc(A_514)
      | ~ v2_pre_topc(A_514)
      | v2_struct_0(A_514) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_399])).

tff(c_406,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_402])).

tff(c_416,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_46,c_38,c_406])).

tff(c_417,plain,(
    k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_416])).

tff(c_281,plain,(
    ! [A_493,B_494,C_495,D_496] :
      ( k2_partfun1(u1_struct_0(A_493),u1_struct_0(B_494),C_495,u1_struct_0(D_496)) = k2_tmap_1(A_493,B_494,C_495,D_496)
      | ~ m1_pre_topc(D_496,A_493)
      | ~ m1_subset_1(C_495,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_493),u1_struct_0(B_494))))
      | ~ v1_funct_2(C_495,u1_struct_0(A_493),u1_struct_0(B_494))
      | ~ v1_funct_1(C_495)
      | ~ l1_pre_topc(B_494)
      | ~ v2_pre_topc(B_494)
      | v2_struct_0(B_494)
      | ~ l1_pre_topc(A_493)
      | ~ v2_pre_topc(A_493)
      | v2_struct_0(A_493) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_283,plain,(
    ! [D_496] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0(D_496)) = k2_tmap_1('#skF_4','#skF_1','#skF_5',D_496)
      | ~ m1_pre_topc(D_496,'#skF_4')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_40,c_281])).

tff(c_289,plain,(
    ! [D_496] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0(D_496)) = k2_tmap_1('#skF_4','#skF_1','#skF_5',D_496)
      | ~ m1_pre_topc(D_496,'#skF_4')
      | v2_struct_0('#skF_1')
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_101,c_62,c_60,c_44,c_42,c_283])).

tff(c_290,plain,(
    ! [D_496] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0(D_496)) = k2_tmap_1('#skF_4','#skF_1','#skF_5',D_496)
      | ~ m1_pre_topc(D_496,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_64,c_289])).

tff(c_429,plain,
    ( k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5') = k2_tmap_1('#skF_4','#skF_1','#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_417,c_290])).

tff(c_436,plain,(
    k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5') = k2_tmap_1('#skF_4','#skF_1','#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_429])).

tff(c_441,plain,(
    r1_tmap_1('#skF_3','#skF_1',k2_tmap_1('#skF_4','#skF_1','#skF_5','#skF_3'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_436,c_114])).

tff(c_463,plain,(
    ! [C_518,B_521,D_517,E_519,G_520,A_516] :
      ( r1_tmap_1(B_521,A_516,C_518,G_520)
      | ~ r1_tmap_1(D_517,A_516,k2_tmap_1(B_521,A_516,C_518,D_517),G_520)
      | ~ r1_tarski(E_519,u1_struct_0(D_517))
      | ~ r2_hidden(G_520,E_519)
      | ~ v3_pre_topc(E_519,B_521)
      | ~ m1_subset_1(G_520,u1_struct_0(D_517))
      | ~ m1_subset_1(G_520,u1_struct_0(B_521))
      | ~ m1_subset_1(E_519,k1_zfmisc_1(u1_struct_0(B_521)))
      | ~ m1_pre_topc(D_517,B_521)
      | v2_struct_0(D_517)
      | ~ m1_subset_1(C_518,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_521),u1_struct_0(A_516))))
      | ~ v1_funct_2(C_518,u1_struct_0(B_521),u1_struct_0(A_516))
      | ~ v1_funct_1(C_518)
      | ~ l1_pre_topc(B_521)
      | ~ v2_pre_topc(B_521)
      | v2_struct_0(B_521)
      | ~ l1_pre_topc(A_516)
      | ~ v2_pre_topc(A_516)
      | v2_struct_0(A_516) ) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_465,plain,(
    ! [E_519] :
      ( r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_8')
      | ~ r1_tarski(E_519,u1_struct_0('#skF_3'))
      | ~ r2_hidden('#skF_8',E_519)
      | ~ v3_pre_topc(E_519,'#skF_4')
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
      | ~ m1_subset_1(E_519,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_pre_topc('#skF_3','#skF_4')
      | v2_struct_0('#skF_3')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'))))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_441,c_463])).

tff(c_468,plain,(
    ! [E_519] :
      ( r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_8')
      | ~ r1_tarski(E_519,u1_struct_0('#skF_3'))
      | ~ r2_hidden('#skF_8',E_519)
      | ~ v3_pre_topc(E_519,'#skF_4')
      | ~ m1_subset_1(E_519,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_130,c_101,c_44,c_42,c_40,c_38,c_75,c_32,c_465])).

tff(c_470,plain,(
    ! [E_522] :
      ( ~ r1_tarski(E_522,u1_struct_0('#skF_3'))
      | ~ r2_hidden('#skF_8',E_522)
      | ~ v3_pre_topc(E_522,'#skF_4')
      | ~ m1_subset_1(E_522,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_48,c_52,c_163,c_468])).

tff(c_510,plain,(
    ! [A_523] :
      ( ~ r2_hidden('#skF_8',A_523)
      | ~ v3_pre_topc(A_523,'#skF_4')
      | ~ r1_tarski(A_523,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_199,c_470])).

tff(c_521,plain,
    ( ~ r2_hidden('#skF_8','#skF_6')
    | ~ v3_pre_topc('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_510])).

tff(c_530,plain,(
    ~ v3_pre_topc('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_521])).

tff(c_224,plain,(
    ! [A_485] :
      ( m1_subset_1(A_485,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_tarski(A_485,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_189])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | ~ m1_subset_1(A_1,k1_zfmisc_1(B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_235,plain,(
    ! [A_486] :
      ( r1_tarski(A_486,u1_struct_0('#skF_4'))
      | ~ r1_tarski(A_486,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_224,c_2])).

tff(c_246,plain,(
    r1_tarski('#skF_6',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_26,c_235])).

tff(c_30,plain,(
    v3_pre_topc('#skF_6','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_250])).

tff(c_36,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_250])).

tff(c_208,plain,(
    ! [D_481,C_482,A_483] :
      ( v3_pre_topc(D_481,C_482)
      | ~ m1_subset_1(D_481,k1_zfmisc_1(u1_struct_0(C_482)))
      | ~ v3_pre_topc(D_481,A_483)
      | ~ m1_pre_topc(C_482,A_483)
      | ~ m1_subset_1(D_481,k1_zfmisc_1(u1_struct_0(A_483)))
      | ~ l1_pre_topc(A_483) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_659,plain,(
    ! [A_545,C_546,A_547] :
      ( v3_pre_topc(A_545,C_546)
      | ~ v3_pre_topc(A_545,A_547)
      | ~ m1_pre_topc(C_546,A_547)
      | ~ m1_subset_1(A_545,k1_zfmisc_1(u1_struct_0(A_547)))
      | ~ l1_pre_topc(A_547)
      | ~ r1_tarski(A_545,u1_struct_0(C_546)) ) ),
    inference(resolution,[status(thm)],[c_4,c_208])).

tff(c_665,plain,(
    ! [A_545] :
      ( v3_pre_topc(A_545,'#skF_4')
      | ~ v3_pre_topc(A_545,'#skF_2')
      | ~ m1_subset_1(A_545,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ r1_tarski(A_545,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_46,c_659])).

tff(c_766,plain,(
    ! [A_558] :
      ( v3_pre_topc(A_558,'#skF_4')
      | ~ v3_pre_topc(A_558,'#skF_2')
      | ~ m1_subset_1(A_558,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ r1_tarski(A_558,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_665])).

tff(c_795,plain,
    ( v3_pre_topc('#skF_6','#skF_4')
    | ~ v3_pre_topc('#skF_6','#skF_2')
    | ~ r1_tarski('#skF_6',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_36,c_766])).

tff(c_814,plain,(
    v3_pre_topc('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_246,c_30,c_795])).

tff(c_816,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_530,c_814])).

tff(c_817,plain,(
    r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_8') ),
    inference(splitRight,[status(thm)],[c_73])).

tff(c_852,plain,(
    ! [C_564,A_565,B_566] :
      ( m1_subset_1(C_564,k1_zfmisc_1(u1_struct_0(A_565)))
      | ~ m1_subset_1(C_564,k1_zfmisc_1(u1_struct_0(B_566)))
      | ~ m1_pre_topc(B_566,A_565)
      | ~ l1_pre_topc(A_565) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_885,plain,(
    ! [A_572,A_573,B_574] :
      ( m1_subset_1(A_572,k1_zfmisc_1(u1_struct_0(A_573)))
      | ~ m1_pre_topc(B_574,A_573)
      | ~ l1_pre_topc(A_573)
      | ~ r1_tarski(A_572,u1_struct_0(B_574)) ) ),
    inference(resolution,[status(thm)],[c_4,c_852])).

tff(c_893,plain,(
    ! [A_572] :
      ( m1_subset_1(A_572,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4')
      | ~ r1_tarski(A_572,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_38,c_885])).

tff(c_903,plain,(
    ! [A_572] :
      ( m1_subset_1(A_572,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_tarski(A_572,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_893])).

tff(c_913,plain,(
    ! [A_577] :
      ( m1_subset_1(A_577,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_tarski(A_577,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_893])).

tff(c_939,plain,(
    ! [A_581] :
      ( r1_tarski(A_581,u1_struct_0('#skF_4'))
      | ~ r1_tarski(A_581,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_913,c_2])).

tff(c_950,plain,(
    r1_tarski('#skF_6',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_26,c_939])).

tff(c_921,plain,(
    ! [D_578,C_579,A_580] :
      ( v3_pre_topc(D_578,C_579)
      | ~ m1_subset_1(D_578,k1_zfmisc_1(u1_struct_0(C_579)))
      | ~ v3_pre_topc(D_578,A_580)
      | ~ m1_pre_topc(C_579,A_580)
      | ~ m1_subset_1(D_578,k1_zfmisc_1(u1_struct_0(A_580)))
      | ~ l1_pre_topc(A_580) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1276,plain,(
    ! [A_630,C_631,A_632] :
      ( v3_pre_topc(A_630,C_631)
      | ~ v3_pre_topc(A_630,A_632)
      | ~ m1_pre_topc(C_631,A_632)
      | ~ m1_subset_1(A_630,k1_zfmisc_1(u1_struct_0(A_632)))
      | ~ l1_pre_topc(A_632)
      | ~ r1_tarski(A_630,u1_struct_0(C_631)) ) ),
    inference(resolution,[status(thm)],[c_4,c_921])).

tff(c_1282,plain,(
    ! [A_630] :
      ( v3_pre_topc(A_630,'#skF_4')
      | ~ v3_pre_topc(A_630,'#skF_2')
      | ~ m1_subset_1(A_630,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ r1_tarski(A_630,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_46,c_1276])).

tff(c_1415,plain,(
    ! [A_649] :
      ( v3_pre_topc(A_649,'#skF_4')
      | ~ v3_pre_topc(A_649,'#skF_2')
      | ~ m1_subset_1(A_649,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ r1_tarski(A_649,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1282])).

tff(c_1444,plain,
    ( v3_pre_topc('#skF_6','#skF_4')
    | ~ v3_pre_topc('#skF_6','#skF_2')
    | ~ r1_tarski('#skF_6',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_36,c_1415])).

tff(c_1462,plain,(
    v3_pre_topc('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_950,c_30,c_1444])).

tff(c_819,plain,(
    ! [B_559,A_560] :
      ( v2_pre_topc(B_559)
      | ~ m1_pre_topc(B_559,A_560)
      | ~ l1_pre_topc(A_560)
      | ~ v2_pre_topc(A_560) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_825,plain,
    ( v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_819])).

tff(c_834,plain,(
    v2_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_825])).

tff(c_1295,plain,(
    ! [B_638,D_634,E_636,A_633,G_637,C_635] :
      ( r1_tmap_1(D_634,A_633,k2_tmap_1(B_638,A_633,C_635,D_634),G_637)
      | ~ r1_tmap_1(B_638,A_633,C_635,G_637)
      | ~ r1_tarski(E_636,u1_struct_0(D_634))
      | ~ r2_hidden(G_637,E_636)
      | ~ v3_pre_topc(E_636,B_638)
      | ~ m1_subset_1(G_637,u1_struct_0(D_634))
      | ~ m1_subset_1(G_637,u1_struct_0(B_638))
      | ~ m1_subset_1(E_636,k1_zfmisc_1(u1_struct_0(B_638)))
      | ~ m1_pre_topc(D_634,B_638)
      | v2_struct_0(D_634)
      | ~ m1_subset_1(C_635,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_638),u1_struct_0(A_633))))
      | ~ v1_funct_2(C_635,u1_struct_0(B_638),u1_struct_0(A_633))
      | ~ v1_funct_1(C_635)
      | ~ l1_pre_topc(B_638)
      | ~ v2_pre_topc(B_638)
      | v2_struct_0(B_638)
      | ~ l1_pre_topc(A_633)
      | ~ v2_pre_topc(A_633)
      | v2_struct_0(A_633) ) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_1309,plain,(
    ! [A_633,B_638,C_635,G_637] :
      ( r1_tmap_1('#skF_3',A_633,k2_tmap_1(B_638,A_633,C_635,'#skF_3'),G_637)
      | ~ r1_tmap_1(B_638,A_633,C_635,G_637)
      | ~ r2_hidden(G_637,'#skF_6')
      | ~ v3_pre_topc('#skF_6',B_638)
      | ~ m1_subset_1(G_637,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(G_637,u1_struct_0(B_638))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0(B_638)))
      | ~ m1_pre_topc('#skF_3',B_638)
      | v2_struct_0('#skF_3')
      | ~ m1_subset_1(C_635,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_638),u1_struct_0(A_633))))
      | ~ v1_funct_2(C_635,u1_struct_0(B_638),u1_struct_0(A_633))
      | ~ v1_funct_1(C_635)
      | ~ l1_pre_topc(B_638)
      | ~ v2_pre_topc(B_638)
      | v2_struct_0(B_638)
      | ~ l1_pre_topc(A_633)
      | ~ v2_pre_topc(A_633)
      | v2_struct_0(A_633) ) ),
    inference(resolution,[status(thm)],[c_26,c_1295])).

tff(c_1376,plain,(
    ! [A_640,B_641,C_642,G_643] :
      ( r1_tmap_1('#skF_3',A_640,k2_tmap_1(B_641,A_640,C_642,'#skF_3'),G_643)
      | ~ r1_tmap_1(B_641,A_640,C_642,G_643)
      | ~ r2_hidden(G_643,'#skF_6')
      | ~ v3_pre_topc('#skF_6',B_641)
      | ~ m1_subset_1(G_643,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(G_643,u1_struct_0(B_641))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0(B_641)))
      | ~ m1_pre_topc('#skF_3',B_641)
      | ~ m1_subset_1(C_642,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_641),u1_struct_0(A_640))))
      | ~ v1_funct_2(C_642,u1_struct_0(B_641),u1_struct_0(A_640))
      | ~ v1_funct_1(C_642)
      | ~ l1_pre_topc(B_641)
      | ~ v2_pre_topc(B_641)
      | v2_struct_0(B_641)
      | ~ l1_pre_topc(A_640)
      | ~ v2_pre_topc(A_640)
      | v2_struct_0(A_640) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_1309])).

tff(c_1378,plain,(
    ! [G_643] :
      ( r1_tmap_1('#skF_3','#skF_1',k2_tmap_1('#skF_4','#skF_1','#skF_5','#skF_3'),G_643)
      | ~ r1_tmap_1('#skF_4','#skF_1','#skF_5',G_643)
      | ~ r2_hidden(G_643,'#skF_6')
      | ~ v3_pre_topc('#skF_6','#skF_4')
      | ~ m1_subset_1(G_643,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(G_643,u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_pre_topc('#skF_3','#skF_4')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_40,c_1376])).

tff(c_1384,plain,(
    ! [G_643] :
      ( r1_tmap_1('#skF_3','#skF_1',k2_tmap_1('#skF_4','#skF_1','#skF_5','#skF_3'),G_643)
      | ~ r1_tmap_1('#skF_4','#skF_1','#skF_5',G_643)
      | ~ r2_hidden(G_643,'#skF_6')
      | ~ v3_pre_topc('#skF_6','#skF_4')
      | ~ m1_subset_1(G_643,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(G_643,u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_834,c_101,c_44,c_42,c_38,c_1378])).

tff(c_1385,plain,(
    ! [G_643] :
      ( r1_tmap_1('#skF_3','#skF_1',k2_tmap_1('#skF_4','#skF_1','#skF_5','#skF_3'),G_643)
      | ~ r1_tmap_1('#skF_4','#skF_1','#skF_5',G_643)
      | ~ r2_hidden(G_643,'#skF_6')
      | ~ v3_pre_topc('#skF_6','#skF_4')
      | ~ m1_subset_1(G_643,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(G_643,u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_48,c_1384])).

tff(c_1465,plain,(
    ! [G_643] :
      ( r1_tmap_1('#skF_3','#skF_1',k2_tmap_1('#skF_4','#skF_1','#skF_5','#skF_3'),G_643)
      | ~ r1_tmap_1('#skF_4','#skF_1','#skF_5',G_643)
      | ~ r2_hidden(G_643,'#skF_6')
      | ~ m1_subset_1(G_643,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(G_643,u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1462,c_1385])).

tff(c_1466,plain,(
    ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_1465])).

tff(c_1478,plain,(
    ~ r1_tarski('#skF_6',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_903,c_1466])).

tff(c_1497,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_1478])).

tff(c_2089,plain,(
    ! [G_699] :
      ( r1_tmap_1('#skF_3','#skF_1',k2_tmap_1('#skF_4','#skF_1','#skF_5','#skF_3'),G_699)
      | ~ r1_tmap_1('#skF_4','#skF_1','#skF_5',G_699)
      | ~ r2_hidden(G_699,'#skF_6')
      | ~ m1_subset_1(G_699,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(G_699,u1_struct_0('#skF_4')) ) ),
    inference(splitRight,[status(thm)],[c_1465])).

tff(c_1095,plain,(
    ! [C_604,B_605,E_607,A_608,D_606] :
      ( k3_tmap_1(A_608,B_605,C_604,D_606,E_607) = k2_partfun1(u1_struct_0(C_604),u1_struct_0(B_605),E_607,u1_struct_0(D_606))
      | ~ m1_pre_topc(D_606,C_604)
      | ~ m1_subset_1(E_607,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_604),u1_struct_0(B_605))))
      | ~ v1_funct_2(E_607,u1_struct_0(C_604),u1_struct_0(B_605))
      | ~ v1_funct_1(E_607)
      | ~ m1_pre_topc(D_606,A_608)
      | ~ m1_pre_topc(C_604,A_608)
      | ~ l1_pre_topc(B_605)
      | ~ v2_pre_topc(B_605)
      | v2_struct_0(B_605)
      | ~ l1_pre_topc(A_608)
      | ~ v2_pre_topc(A_608)
      | v2_struct_0(A_608) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_1097,plain,(
    ! [A_608,D_606] :
      ( k3_tmap_1(A_608,'#skF_1','#skF_4',D_606,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0(D_606))
      | ~ m1_pre_topc(D_606,'#skF_4')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_606,A_608)
      | ~ m1_pre_topc('#skF_4',A_608)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1')
      | ~ l1_pre_topc(A_608)
      | ~ v2_pre_topc(A_608)
      | v2_struct_0(A_608) ) ),
    inference(resolution,[status(thm)],[c_40,c_1095])).

tff(c_1103,plain,(
    ! [A_608,D_606] :
      ( k3_tmap_1(A_608,'#skF_1','#skF_4',D_606,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0(D_606))
      | ~ m1_pre_topc(D_606,'#skF_4')
      | ~ m1_pre_topc(D_606,A_608)
      | ~ m1_pre_topc('#skF_4',A_608)
      | v2_struct_0('#skF_1')
      | ~ l1_pre_topc(A_608)
      | ~ v2_pre_topc(A_608)
      | v2_struct_0(A_608) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_44,c_42,c_1097])).

tff(c_1148,plain,(
    ! [A_614,D_615] :
      ( k3_tmap_1(A_614,'#skF_1','#skF_4',D_615,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0(D_615))
      | ~ m1_pre_topc(D_615,'#skF_4')
      | ~ m1_pre_topc(D_615,A_614)
      | ~ m1_pre_topc('#skF_4',A_614)
      | ~ l1_pre_topc(A_614)
      | ~ v2_pre_topc(A_614)
      | v2_struct_0(A_614) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_1103])).

tff(c_1152,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_1148])).

tff(c_1162,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_46,c_38,c_1152])).

tff(c_1163,plain,(
    k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_1162])).

tff(c_1006,plain,(
    ! [A_592,B_593,C_594,D_595] :
      ( k2_partfun1(u1_struct_0(A_592),u1_struct_0(B_593),C_594,u1_struct_0(D_595)) = k2_tmap_1(A_592,B_593,C_594,D_595)
      | ~ m1_pre_topc(D_595,A_592)
      | ~ m1_subset_1(C_594,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_592),u1_struct_0(B_593))))
      | ~ v1_funct_2(C_594,u1_struct_0(A_592),u1_struct_0(B_593))
      | ~ v1_funct_1(C_594)
      | ~ l1_pre_topc(B_593)
      | ~ v2_pre_topc(B_593)
      | v2_struct_0(B_593)
      | ~ l1_pre_topc(A_592)
      | ~ v2_pre_topc(A_592)
      | v2_struct_0(A_592) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_1008,plain,(
    ! [D_595] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0(D_595)) = k2_tmap_1('#skF_4','#skF_1','#skF_5',D_595)
      | ~ m1_pre_topc(D_595,'#skF_4')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_40,c_1006])).

tff(c_1014,plain,(
    ! [D_595] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0(D_595)) = k2_tmap_1('#skF_4','#skF_1','#skF_5',D_595)
      | ~ m1_pre_topc(D_595,'#skF_4')
      | v2_struct_0('#skF_1')
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_834,c_101,c_62,c_60,c_44,c_42,c_1008])).

tff(c_1015,plain,(
    ! [D_595] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0(D_595)) = k2_tmap_1('#skF_4','#skF_1','#skF_5',D_595)
      | ~ m1_pre_topc(D_595,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_64,c_1014])).

tff(c_1175,plain,
    ( k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5') = k2_tmap_1('#skF_4','#skF_1','#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1163,c_1015])).

tff(c_1182,plain,(
    k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5') = k2_tmap_1('#skF_4','#skF_1','#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_1175])).

tff(c_839,plain,(
    ~ r1_tmap_1('#skF_3','#skF_1',k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_817,c_74])).

tff(c_1187,plain,(
    ~ r1_tmap_1('#skF_3','#skF_1',k2_tmap_1('#skF_4','#skF_1','#skF_5','#skF_3'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1182,c_839])).

tff(c_2094,plain,
    ( ~ r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_8')
    | ~ r2_hidden('#skF_8','#skF_6')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_2089,c_1187])).

tff(c_2102,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_32,c_76,c_817,c_2094])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:00:20 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.05/1.84  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.05/1.85  
% 5.05/1.85  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.05/1.85  %$ r1_tmap_1 > v1_funct_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4
% 5.05/1.85  
% 5.05/1.85  %Foreground sorts:
% 5.05/1.85  
% 5.05/1.85  
% 5.05/1.85  %Background operators:
% 5.05/1.85  
% 5.05/1.85  
% 5.05/1.85  %Foreground operators:
% 5.05/1.85  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.05/1.85  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 5.05/1.85  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.05/1.85  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 5.05/1.85  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.05/1.85  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.05/1.85  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 5.05/1.85  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.05/1.85  tff('#skF_7', type, '#skF_7': $i).
% 5.05/1.85  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.05/1.85  tff('#skF_5', type, '#skF_5': $i).
% 5.05/1.85  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.05/1.85  tff('#skF_6', type, '#skF_6': $i).
% 5.05/1.85  tff('#skF_2', type, '#skF_2': $i).
% 5.05/1.85  tff('#skF_3', type, '#skF_3': $i).
% 5.05/1.85  tff('#skF_1', type, '#skF_1': $i).
% 5.05/1.85  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.05/1.85  tff('#skF_8', type, '#skF_8': $i).
% 5.05/1.85  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.05/1.85  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.05/1.85  tff('#skF_4', type, '#skF_4': $i).
% 5.05/1.85  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.05/1.85  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 5.05/1.85  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 5.05/1.85  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.05/1.85  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 5.05/1.85  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.05/1.85  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.05/1.85  
% 5.05/1.88  tff(f_250, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, B)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(A))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(A))))) => (m1_pre_topc(C, D) => (![F]: (m1_subset_1(F, k1_zfmisc_1(u1_struct_0(B))) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (![H]: (m1_subset_1(H, u1_struct_0(C)) => ((((v3_pre_topc(F, B) & r2_hidden(G, F)) & r1_tarski(F, u1_struct_0(C))) & (G = H)) => (r1_tmap_1(D, A, E, G) <=> r1_tmap_1(C, A, k3_tmap_1(B, A, D, C, E), H)))))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t85_tmap_1)).
% 5.05/1.88  tff(f_45, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 5.05/1.88  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 5.05/1.88  tff(f_55, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B))) => m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_pre_topc)).
% 5.05/1.88  tff(f_38, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_pre_topc)).
% 5.05/1.88  tff(f_131, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (m1_pre_topc(C, A) => (![D]: (m1_pre_topc(D, A) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (m1_pre_topc(D, C) => (k3_tmap_1(A, B, C, D, E) = k2_partfun1(u1_struct_0(C), u1_struct_0(B), E, u1_struct_0(D)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tmap_1)).
% 5.05/1.88  tff(f_99, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tmap_1)).
% 5.05/1.88  tff(f_180, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(B))) => (![F]: (m1_subset_1(F, u1_struct_0(B)) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => ((((v3_pre_topc(E, B) & r2_hidden(F, E)) & r1_tarski(E, u1_struct_0(D))) & (F = G)) => (r1_tmap_1(B, A, C, F) <=> r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), G))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_tmap_1)).
% 5.05/1.88  tff(f_72, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_pre_topc(C, A) => (v3_pre_topc(B, A) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(C))) => ((D = B) => v3_pre_topc(D, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_tops_2)).
% 5.05/1.88  tff(c_24, plain, ('#skF_7'='#skF_8'), inference(cnfTransformation, [status(thm)], [f_250])).
% 5.05/1.88  tff(c_34, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_250])).
% 5.05/1.88  tff(c_75, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_34])).
% 5.05/1.88  tff(c_32, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_250])).
% 5.05/1.88  tff(c_28, plain, (r2_hidden('#skF_7', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_250])).
% 5.05/1.88  tff(c_76, plain, (r2_hidden('#skF_8', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_28])).
% 5.05/1.88  tff(c_26, plain, (r1_tarski('#skF_6', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_250])).
% 5.05/1.88  tff(c_54, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_250])).
% 5.05/1.88  tff(c_46, plain, (m1_pre_topc('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_250])).
% 5.05/1.88  tff(c_86, plain, (![B_460, A_461]: (l1_pre_topc(B_460) | ~m1_pre_topc(B_460, A_461) | ~l1_pre_topc(A_461))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.05/1.88  tff(c_92, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_46, c_86])).
% 5.05/1.88  tff(c_101, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_92])).
% 5.05/1.88  tff(c_38, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_250])).
% 5.05/1.88  tff(c_4, plain, (![A_1, B_2]: (m1_subset_1(A_1, k1_zfmisc_1(B_2)) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.05/1.88  tff(c_164, plain, (![C_472, A_473, B_474]: (m1_subset_1(C_472, k1_zfmisc_1(u1_struct_0(A_473))) | ~m1_subset_1(C_472, k1_zfmisc_1(u1_struct_0(B_474))) | ~m1_pre_topc(B_474, A_473) | ~l1_pre_topc(A_473))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.05/1.88  tff(c_181, plain, (![A_477, A_478, B_479]: (m1_subset_1(A_477, k1_zfmisc_1(u1_struct_0(A_478))) | ~m1_pre_topc(B_479, A_478) | ~l1_pre_topc(A_478) | ~r1_tarski(A_477, u1_struct_0(B_479)))), inference(resolution, [status(thm)], [c_4, c_164])).
% 5.05/1.88  tff(c_189, plain, (![A_477]: (m1_subset_1(A_477, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4') | ~r1_tarski(A_477, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_38, c_181])).
% 5.05/1.88  tff(c_199, plain, (![A_477]: (m1_subset_1(A_477, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r1_tarski(A_477, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_101, c_189])).
% 5.05/1.88  tff(c_64, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_250])).
% 5.05/1.88  tff(c_48, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_250])).
% 5.05/1.88  tff(c_52, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_250])).
% 5.05/1.88  tff(c_72, plain, (r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_7') | r1_tmap_1('#skF_3', '#skF_1', k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_250])).
% 5.05/1.88  tff(c_73, plain, (r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_8') | r1_tmap_1('#skF_3', '#skF_1', k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_72])).
% 5.05/1.88  tff(c_114, plain, (r1_tmap_1('#skF_3', '#skF_1', k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5'), '#skF_8')), inference(splitLeft, [status(thm)], [c_73])).
% 5.05/1.88  tff(c_66, plain, (~r1_tmap_1('#skF_3', '#skF_1', k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5'), '#skF_8') | ~r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_250])).
% 5.05/1.88  tff(c_74, plain, (~r1_tmap_1('#skF_3', '#skF_1', k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5'), '#skF_8') | ~r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_66])).
% 5.05/1.88  tff(c_163, plain, (~r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_114, c_74])).
% 5.05/1.88  tff(c_62, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_250])).
% 5.05/1.88  tff(c_60, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_250])).
% 5.05/1.88  tff(c_56, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_250])).
% 5.05/1.88  tff(c_115, plain, (![B_464, A_465]: (v2_pre_topc(B_464) | ~m1_pre_topc(B_464, A_465) | ~l1_pre_topc(A_465) | ~v2_pre_topc(A_465))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.05/1.88  tff(c_121, plain, (v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_46, c_115])).
% 5.05/1.88  tff(c_130, plain, (v2_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_121])).
% 5.05/1.88  tff(c_44, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_250])).
% 5.05/1.88  tff(c_42, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_250])).
% 5.05/1.88  tff(c_40, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_250])).
% 5.05/1.88  tff(c_58, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_250])).
% 5.05/1.88  tff(c_50, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_250])).
% 5.05/1.88  tff(c_391, plain, (![D_511, B_510, E_512, C_509, A_513]: (k3_tmap_1(A_513, B_510, C_509, D_511, E_512)=k2_partfun1(u1_struct_0(C_509), u1_struct_0(B_510), E_512, u1_struct_0(D_511)) | ~m1_pre_topc(D_511, C_509) | ~m1_subset_1(E_512, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_509), u1_struct_0(B_510)))) | ~v1_funct_2(E_512, u1_struct_0(C_509), u1_struct_0(B_510)) | ~v1_funct_1(E_512) | ~m1_pre_topc(D_511, A_513) | ~m1_pre_topc(C_509, A_513) | ~l1_pre_topc(B_510) | ~v2_pre_topc(B_510) | v2_struct_0(B_510) | ~l1_pre_topc(A_513) | ~v2_pre_topc(A_513) | v2_struct_0(A_513))), inference(cnfTransformation, [status(thm)], [f_131])).
% 5.05/1.88  tff(c_393, plain, (![A_513, D_511]: (k3_tmap_1(A_513, '#skF_1', '#skF_4', D_511, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0(D_511)) | ~m1_pre_topc(D_511, '#skF_4') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_511, A_513) | ~m1_pre_topc('#skF_4', A_513) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~l1_pre_topc(A_513) | ~v2_pre_topc(A_513) | v2_struct_0(A_513))), inference(resolution, [status(thm)], [c_40, c_391])).
% 5.05/1.88  tff(c_399, plain, (![A_513, D_511]: (k3_tmap_1(A_513, '#skF_1', '#skF_4', D_511, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0(D_511)) | ~m1_pre_topc(D_511, '#skF_4') | ~m1_pre_topc(D_511, A_513) | ~m1_pre_topc('#skF_4', A_513) | v2_struct_0('#skF_1') | ~l1_pre_topc(A_513) | ~v2_pre_topc(A_513) | v2_struct_0(A_513))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_44, c_42, c_393])).
% 5.05/1.88  tff(c_402, plain, (![A_514, D_515]: (k3_tmap_1(A_514, '#skF_1', '#skF_4', D_515, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0(D_515)) | ~m1_pre_topc(D_515, '#skF_4') | ~m1_pre_topc(D_515, A_514) | ~m1_pre_topc('#skF_4', A_514) | ~l1_pre_topc(A_514) | ~v2_pre_topc(A_514) | v2_struct_0(A_514))), inference(negUnitSimplification, [status(thm)], [c_64, c_399])).
% 5.05/1.88  tff(c_406, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5') | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_50, c_402])).
% 5.05/1.88  tff(c_416, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_46, c_38, c_406])).
% 5.05/1.88  tff(c_417, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_58, c_416])).
% 5.05/1.88  tff(c_281, plain, (![A_493, B_494, C_495, D_496]: (k2_partfun1(u1_struct_0(A_493), u1_struct_0(B_494), C_495, u1_struct_0(D_496))=k2_tmap_1(A_493, B_494, C_495, D_496) | ~m1_pre_topc(D_496, A_493) | ~m1_subset_1(C_495, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_493), u1_struct_0(B_494)))) | ~v1_funct_2(C_495, u1_struct_0(A_493), u1_struct_0(B_494)) | ~v1_funct_1(C_495) | ~l1_pre_topc(B_494) | ~v2_pre_topc(B_494) | v2_struct_0(B_494) | ~l1_pre_topc(A_493) | ~v2_pre_topc(A_493) | v2_struct_0(A_493))), inference(cnfTransformation, [status(thm)], [f_99])).
% 5.05/1.88  tff(c_283, plain, (![D_496]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0(D_496))=k2_tmap_1('#skF_4', '#skF_1', '#skF_5', D_496) | ~m1_pre_topc(D_496, '#skF_4') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_40, c_281])).
% 5.05/1.88  tff(c_289, plain, (![D_496]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0(D_496))=k2_tmap_1('#skF_4', '#skF_1', '#skF_5', D_496) | ~m1_pre_topc(D_496, '#skF_4') | v2_struct_0('#skF_1') | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_130, c_101, c_62, c_60, c_44, c_42, c_283])).
% 5.05/1.88  tff(c_290, plain, (![D_496]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0(D_496))=k2_tmap_1('#skF_4', '#skF_1', '#skF_5', D_496) | ~m1_pre_topc(D_496, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_48, c_64, c_289])).
% 5.05/1.88  tff(c_429, plain, (k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5')=k2_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_417, c_290])).
% 5.05/1.88  tff(c_436, plain, (k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5')=k2_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_429])).
% 5.05/1.88  tff(c_441, plain, (r1_tmap_1('#skF_3', '#skF_1', k2_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_3'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_436, c_114])).
% 5.05/1.88  tff(c_463, plain, (![C_518, B_521, D_517, E_519, G_520, A_516]: (r1_tmap_1(B_521, A_516, C_518, G_520) | ~r1_tmap_1(D_517, A_516, k2_tmap_1(B_521, A_516, C_518, D_517), G_520) | ~r1_tarski(E_519, u1_struct_0(D_517)) | ~r2_hidden(G_520, E_519) | ~v3_pre_topc(E_519, B_521) | ~m1_subset_1(G_520, u1_struct_0(D_517)) | ~m1_subset_1(G_520, u1_struct_0(B_521)) | ~m1_subset_1(E_519, k1_zfmisc_1(u1_struct_0(B_521))) | ~m1_pre_topc(D_517, B_521) | v2_struct_0(D_517) | ~m1_subset_1(C_518, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_521), u1_struct_0(A_516)))) | ~v1_funct_2(C_518, u1_struct_0(B_521), u1_struct_0(A_516)) | ~v1_funct_1(C_518) | ~l1_pre_topc(B_521) | ~v2_pre_topc(B_521) | v2_struct_0(B_521) | ~l1_pre_topc(A_516) | ~v2_pre_topc(A_516) | v2_struct_0(A_516))), inference(cnfTransformation, [status(thm)], [f_180])).
% 5.05/1.88  tff(c_465, plain, (![E_519]: (r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_8') | ~r1_tarski(E_519, u1_struct_0('#skF_3')) | ~r2_hidden('#skF_8', E_519) | ~v3_pre_topc(E_519, '#skF_4') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~m1_subset_1(E_519, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_pre_topc('#skF_3', '#skF_4') | v2_struct_0('#skF_3') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_441, c_463])).
% 5.05/1.88  tff(c_468, plain, (![E_519]: (r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_8') | ~r1_tarski(E_519, u1_struct_0('#skF_3')) | ~r2_hidden('#skF_8', E_519) | ~v3_pre_topc(E_519, '#skF_4') | ~m1_subset_1(E_519, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_struct_0('#skF_3') | v2_struct_0('#skF_4') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_130, c_101, c_44, c_42, c_40, c_38, c_75, c_32, c_465])).
% 5.05/1.88  tff(c_470, plain, (![E_522]: (~r1_tarski(E_522, u1_struct_0('#skF_3')) | ~r2_hidden('#skF_8', E_522) | ~v3_pre_topc(E_522, '#skF_4') | ~m1_subset_1(E_522, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_64, c_48, c_52, c_163, c_468])).
% 5.05/1.88  tff(c_510, plain, (![A_523]: (~r2_hidden('#skF_8', A_523) | ~v3_pre_topc(A_523, '#skF_4') | ~r1_tarski(A_523, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_199, c_470])).
% 5.05/1.88  tff(c_521, plain, (~r2_hidden('#skF_8', '#skF_6') | ~v3_pre_topc('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_26, c_510])).
% 5.05/1.88  tff(c_530, plain, (~v3_pre_topc('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_521])).
% 5.05/1.88  tff(c_224, plain, (![A_485]: (m1_subset_1(A_485, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r1_tarski(A_485, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_101, c_189])).
% 5.05/1.88  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | ~m1_subset_1(A_1, k1_zfmisc_1(B_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.05/1.88  tff(c_235, plain, (![A_486]: (r1_tarski(A_486, u1_struct_0('#skF_4')) | ~r1_tarski(A_486, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_224, c_2])).
% 5.05/1.88  tff(c_246, plain, (r1_tarski('#skF_6', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_26, c_235])).
% 5.05/1.88  tff(c_30, plain, (v3_pre_topc('#skF_6', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_250])).
% 5.05/1.88  tff(c_36, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_250])).
% 5.05/1.88  tff(c_208, plain, (![D_481, C_482, A_483]: (v3_pre_topc(D_481, C_482) | ~m1_subset_1(D_481, k1_zfmisc_1(u1_struct_0(C_482))) | ~v3_pre_topc(D_481, A_483) | ~m1_pre_topc(C_482, A_483) | ~m1_subset_1(D_481, k1_zfmisc_1(u1_struct_0(A_483))) | ~l1_pre_topc(A_483))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.05/1.88  tff(c_659, plain, (![A_545, C_546, A_547]: (v3_pre_topc(A_545, C_546) | ~v3_pre_topc(A_545, A_547) | ~m1_pre_topc(C_546, A_547) | ~m1_subset_1(A_545, k1_zfmisc_1(u1_struct_0(A_547))) | ~l1_pre_topc(A_547) | ~r1_tarski(A_545, u1_struct_0(C_546)))), inference(resolution, [status(thm)], [c_4, c_208])).
% 5.05/1.88  tff(c_665, plain, (![A_545]: (v3_pre_topc(A_545, '#skF_4') | ~v3_pre_topc(A_545, '#skF_2') | ~m1_subset_1(A_545, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~r1_tarski(A_545, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_46, c_659])).
% 5.05/1.88  tff(c_766, plain, (![A_558]: (v3_pre_topc(A_558, '#skF_4') | ~v3_pre_topc(A_558, '#skF_2') | ~m1_subset_1(A_558, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~r1_tarski(A_558, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_665])).
% 5.05/1.88  tff(c_795, plain, (v3_pre_topc('#skF_6', '#skF_4') | ~v3_pre_topc('#skF_6', '#skF_2') | ~r1_tarski('#skF_6', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_36, c_766])).
% 5.05/1.88  tff(c_814, plain, (v3_pre_topc('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_246, c_30, c_795])).
% 5.05/1.88  tff(c_816, plain, $false, inference(negUnitSimplification, [status(thm)], [c_530, c_814])).
% 5.05/1.88  tff(c_817, plain, (r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_8')), inference(splitRight, [status(thm)], [c_73])).
% 5.05/1.88  tff(c_852, plain, (![C_564, A_565, B_566]: (m1_subset_1(C_564, k1_zfmisc_1(u1_struct_0(A_565))) | ~m1_subset_1(C_564, k1_zfmisc_1(u1_struct_0(B_566))) | ~m1_pre_topc(B_566, A_565) | ~l1_pre_topc(A_565))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.05/1.88  tff(c_885, plain, (![A_572, A_573, B_574]: (m1_subset_1(A_572, k1_zfmisc_1(u1_struct_0(A_573))) | ~m1_pre_topc(B_574, A_573) | ~l1_pre_topc(A_573) | ~r1_tarski(A_572, u1_struct_0(B_574)))), inference(resolution, [status(thm)], [c_4, c_852])).
% 5.05/1.88  tff(c_893, plain, (![A_572]: (m1_subset_1(A_572, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4') | ~r1_tarski(A_572, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_38, c_885])).
% 5.05/1.88  tff(c_903, plain, (![A_572]: (m1_subset_1(A_572, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r1_tarski(A_572, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_101, c_893])).
% 5.05/1.88  tff(c_913, plain, (![A_577]: (m1_subset_1(A_577, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r1_tarski(A_577, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_101, c_893])).
% 5.05/1.88  tff(c_939, plain, (![A_581]: (r1_tarski(A_581, u1_struct_0('#skF_4')) | ~r1_tarski(A_581, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_913, c_2])).
% 5.05/1.88  tff(c_950, plain, (r1_tarski('#skF_6', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_26, c_939])).
% 5.05/1.88  tff(c_921, plain, (![D_578, C_579, A_580]: (v3_pre_topc(D_578, C_579) | ~m1_subset_1(D_578, k1_zfmisc_1(u1_struct_0(C_579))) | ~v3_pre_topc(D_578, A_580) | ~m1_pre_topc(C_579, A_580) | ~m1_subset_1(D_578, k1_zfmisc_1(u1_struct_0(A_580))) | ~l1_pre_topc(A_580))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.05/1.88  tff(c_1276, plain, (![A_630, C_631, A_632]: (v3_pre_topc(A_630, C_631) | ~v3_pre_topc(A_630, A_632) | ~m1_pre_topc(C_631, A_632) | ~m1_subset_1(A_630, k1_zfmisc_1(u1_struct_0(A_632))) | ~l1_pre_topc(A_632) | ~r1_tarski(A_630, u1_struct_0(C_631)))), inference(resolution, [status(thm)], [c_4, c_921])).
% 5.05/1.88  tff(c_1282, plain, (![A_630]: (v3_pre_topc(A_630, '#skF_4') | ~v3_pre_topc(A_630, '#skF_2') | ~m1_subset_1(A_630, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~r1_tarski(A_630, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_46, c_1276])).
% 5.05/1.88  tff(c_1415, plain, (![A_649]: (v3_pre_topc(A_649, '#skF_4') | ~v3_pre_topc(A_649, '#skF_2') | ~m1_subset_1(A_649, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~r1_tarski(A_649, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_1282])).
% 5.05/1.88  tff(c_1444, plain, (v3_pre_topc('#skF_6', '#skF_4') | ~v3_pre_topc('#skF_6', '#skF_2') | ~r1_tarski('#skF_6', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_36, c_1415])).
% 5.05/1.88  tff(c_1462, plain, (v3_pre_topc('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_950, c_30, c_1444])).
% 5.05/1.88  tff(c_819, plain, (![B_559, A_560]: (v2_pre_topc(B_559) | ~m1_pre_topc(B_559, A_560) | ~l1_pre_topc(A_560) | ~v2_pre_topc(A_560))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.05/1.88  tff(c_825, plain, (v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_46, c_819])).
% 5.05/1.88  tff(c_834, plain, (v2_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_825])).
% 5.05/1.88  tff(c_1295, plain, (![B_638, D_634, E_636, A_633, G_637, C_635]: (r1_tmap_1(D_634, A_633, k2_tmap_1(B_638, A_633, C_635, D_634), G_637) | ~r1_tmap_1(B_638, A_633, C_635, G_637) | ~r1_tarski(E_636, u1_struct_0(D_634)) | ~r2_hidden(G_637, E_636) | ~v3_pre_topc(E_636, B_638) | ~m1_subset_1(G_637, u1_struct_0(D_634)) | ~m1_subset_1(G_637, u1_struct_0(B_638)) | ~m1_subset_1(E_636, k1_zfmisc_1(u1_struct_0(B_638))) | ~m1_pre_topc(D_634, B_638) | v2_struct_0(D_634) | ~m1_subset_1(C_635, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_638), u1_struct_0(A_633)))) | ~v1_funct_2(C_635, u1_struct_0(B_638), u1_struct_0(A_633)) | ~v1_funct_1(C_635) | ~l1_pre_topc(B_638) | ~v2_pre_topc(B_638) | v2_struct_0(B_638) | ~l1_pre_topc(A_633) | ~v2_pre_topc(A_633) | v2_struct_0(A_633))), inference(cnfTransformation, [status(thm)], [f_180])).
% 5.05/1.88  tff(c_1309, plain, (![A_633, B_638, C_635, G_637]: (r1_tmap_1('#skF_3', A_633, k2_tmap_1(B_638, A_633, C_635, '#skF_3'), G_637) | ~r1_tmap_1(B_638, A_633, C_635, G_637) | ~r2_hidden(G_637, '#skF_6') | ~v3_pre_topc('#skF_6', B_638) | ~m1_subset_1(G_637, u1_struct_0('#skF_3')) | ~m1_subset_1(G_637, u1_struct_0(B_638)) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0(B_638))) | ~m1_pre_topc('#skF_3', B_638) | v2_struct_0('#skF_3') | ~m1_subset_1(C_635, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_638), u1_struct_0(A_633)))) | ~v1_funct_2(C_635, u1_struct_0(B_638), u1_struct_0(A_633)) | ~v1_funct_1(C_635) | ~l1_pre_topc(B_638) | ~v2_pre_topc(B_638) | v2_struct_0(B_638) | ~l1_pre_topc(A_633) | ~v2_pre_topc(A_633) | v2_struct_0(A_633))), inference(resolution, [status(thm)], [c_26, c_1295])).
% 5.05/1.88  tff(c_1376, plain, (![A_640, B_641, C_642, G_643]: (r1_tmap_1('#skF_3', A_640, k2_tmap_1(B_641, A_640, C_642, '#skF_3'), G_643) | ~r1_tmap_1(B_641, A_640, C_642, G_643) | ~r2_hidden(G_643, '#skF_6') | ~v3_pre_topc('#skF_6', B_641) | ~m1_subset_1(G_643, u1_struct_0('#skF_3')) | ~m1_subset_1(G_643, u1_struct_0(B_641)) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0(B_641))) | ~m1_pre_topc('#skF_3', B_641) | ~m1_subset_1(C_642, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_641), u1_struct_0(A_640)))) | ~v1_funct_2(C_642, u1_struct_0(B_641), u1_struct_0(A_640)) | ~v1_funct_1(C_642) | ~l1_pre_topc(B_641) | ~v2_pre_topc(B_641) | v2_struct_0(B_641) | ~l1_pre_topc(A_640) | ~v2_pre_topc(A_640) | v2_struct_0(A_640))), inference(negUnitSimplification, [status(thm)], [c_52, c_1309])).
% 5.05/1.88  tff(c_1378, plain, (![G_643]: (r1_tmap_1('#skF_3', '#skF_1', k2_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_3'), G_643) | ~r1_tmap_1('#skF_4', '#skF_1', '#skF_5', G_643) | ~r2_hidden(G_643, '#skF_6') | ~v3_pre_topc('#skF_6', '#skF_4') | ~m1_subset_1(G_643, u1_struct_0('#skF_3')) | ~m1_subset_1(G_643, u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_pre_topc('#skF_3', '#skF_4') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_40, c_1376])).
% 5.05/1.88  tff(c_1384, plain, (![G_643]: (r1_tmap_1('#skF_3', '#skF_1', k2_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_3'), G_643) | ~r1_tmap_1('#skF_4', '#skF_1', '#skF_5', G_643) | ~r2_hidden(G_643, '#skF_6') | ~v3_pre_topc('#skF_6', '#skF_4') | ~m1_subset_1(G_643, u1_struct_0('#skF_3')) | ~m1_subset_1(G_643, u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_struct_0('#skF_4') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_834, c_101, c_44, c_42, c_38, c_1378])).
% 5.05/1.88  tff(c_1385, plain, (![G_643]: (r1_tmap_1('#skF_3', '#skF_1', k2_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_3'), G_643) | ~r1_tmap_1('#skF_4', '#skF_1', '#skF_5', G_643) | ~r2_hidden(G_643, '#skF_6') | ~v3_pre_topc('#skF_6', '#skF_4') | ~m1_subset_1(G_643, u1_struct_0('#skF_3')) | ~m1_subset_1(G_643, u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_64, c_48, c_1384])).
% 5.05/1.88  tff(c_1465, plain, (![G_643]: (r1_tmap_1('#skF_3', '#skF_1', k2_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_3'), G_643) | ~r1_tmap_1('#skF_4', '#skF_1', '#skF_5', G_643) | ~r2_hidden(G_643, '#skF_6') | ~m1_subset_1(G_643, u1_struct_0('#skF_3')) | ~m1_subset_1(G_643, u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_1462, c_1385])).
% 5.05/1.88  tff(c_1466, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(splitLeft, [status(thm)], [c_1465])).
% 5.05/1.88  tff(c_1478, plain, (~r1_tarski('#skF_6', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_903, c_1466])).
% 5.05/1.88  tff(c_1497, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_1478])).
% 5.05/1.88  tff(c_2089, plain, (![G_699]: (r1_tmap_1('#skF_3', '#skF_1', k2_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_3'), G_699) | ~r1_tmap_1('#skF_4', '#skF_1', '#skF_5', G_699) | ~r2_hidden(G_699, '#skF_6') | ~m1_subset_1(G_699, u1_struct_0('#skF_3')) | ~m1_subset_1(G_699, u1_struct_0('#skF_4')))), inference(splitRight, [status(thm)], [c_1465])).
% 5.05/1.88  tff(c_1095, plain, (![C_604, B_605, E_607, A_608, D_606]: (k3_tmap_1(A_608, B_605, C_604, D_606, E_607)=k2_partfun1(u1_struct_0(C_604), u1_struct_0(B_605), E_607, u1_struct_0(D_606)) | ~m1_pre_topc(D_606, C_604) | ~m1_subset_1(E_607, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_604), u1_struct_0(B_605)))) | ~v1_funct_2(E_607, u1_struct_0(C_604), u1_struct_0(B_605)) | ~v1_funct_1(E_607) | ~m1_pre_topc(D_606, A_608) | ~m1_pre_topc(C_604, A_608) | ~l1_pre_topc(B_605) | ~v2_pre_topc(B_605) | v2_struct_0(B_605) | ~l1_pre_topc(A_608) | ~v2_pre_topc(A_608) | v2_struct_0(A_608))), inference(cnfTransformation, [status(thm)], [f_131])).
% 5.05/1.88  tff(c_1097, plain, (![A_608, D_606]: (k3_tmap_1(A_608, '#skF_1', '#skF_4', D_606, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0(D_606)) | ~m1_pre_topc(D_606, '#skF_4') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_606, A_608) | ~m1_pre_topc('#skF_4', A_608) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~l1_pre_topc(A_608) | ~v2_pre_topc(A_608) | v2_struct_0(A_608))), inference(resolution, [status(thm)], [c_40, c_1095])).
% 5.05/1.88  tff(c_1103, plain, (![A_608, D_606]: (k3_tmap_1(A_608, '#skF_1', '#skF_4', D_606, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0(D_606)) | ~m1_pre_topc(D_606, '#skF_4') | ~m1_pre_topc(D_606, A_608) | ~m1_pre_topc('#skF_4', A_608) | v2_struct_0('#skF_1') | ~l1_pre_topc(A_608) | ~v2_pre_topc(A_608) | v2_struct_0(A_608))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_44, c_42, c_1097])).
% 5.05/1.88  tff(c_1148, plain, (![A_614, D_615]: (k3_tmap_1(A_614, '#skF_1', '#skF_4', D_615, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0(D_615)) | ~m1_pre_topc(D_615, '#skF_4') | ~m1_pre_topc(D_615, A_614) | ~m1_pre_topc('#skF_4', A_614) | ~l1_pre_topc(A_614) | ~v2_pre_topc(A_614) | v2_struct_0(A_614))), inference(negUnitSimplification, [status(thm)], [c_64, c_1103])).
% 5.05/1.88  tff(c_1152, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5') | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_50, c_1148])).
% 5.05/1.88  tff(c_1162, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_46, c_38, c_1152])).
% 5.05/1.88  tff(c_1163, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_58, c_1162])).
% 5.05/1.88  tff(c_1006, plain, (![A_592, B_593, C_594, D_595]: (k2_partfun1(u1_struct_0(A_592), u1_struct_0(B_593), C_594, u1_struct_0(D_595))=k2_tmap_1(A_592, B_593, C_594, D_595) | ~m1_pre_topc(D_595, A_592) | ~m1_subset_1(C_594, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_592), u1_struct_0(B_593)))) | ~v1_funct_2(C_594, u1_struct_0(A_592), u1_struct_0(B_593)) | ~v1_funct_1(C_594) | ~l1_pre_topc(B_593) | ~v2_pre_topc(B_593) | v2_struct_0(B_593) | ~l1_pre_topc(A_592) | ~v2_pre_topc(A_592) | v2_struct_0(A_592))), inference(cnfTransformation, [status(thm)], [f_99])).
% 5.05/1.88  tff(c_1008, plain, (![D_595]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0(D_595))=k2_tmap_1('#skF_4', '#skF_1', '#skF_5', D_595) | ~m1_pre_topc(D_595, '#skF_4') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_40, c_1006])).
% 5.05/1.88  tff(c_1014, plain, (![D_595]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0(D_595))=k2_tmap_1('#skF_4', '#skF_1', '#skF_5', D_595) | ~m1_pre_topc(D_595, '#skF_4') | v2_struct_0('#skF_1') | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_834, c_101, c_62, c_60, c_44, c_42, c_1008])).
% 5.05/1.88  tff(c_1015, plain, (![D_595]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0(D_595))=k2_tmap_1('#skF_4', '#skF_1', '#skF_5', D_595) | ~m1_pre_topc(D_595, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_48, c_64, c_1014])).
% 5.05/1.88  tff(c_1175, plain, (k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5')=k2_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1163, c_1015])).
% 5.05/1.88  tff(c_1182, plain, (k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5')=k2_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_1175])).
% 5.05/1.88  tff(c_839, plain, (~r1_tmap_1('#skF_3', '#skF_1', k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_817, c_74])).
% 5.05/1.88  tff(c_1187, plain, (~r1_tmap_1('#skF_3', '#skF_1', k2_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_3'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_1182, c_839])).
% 5.05/1.88  tff(c_2094, plain, (~r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_8') | ~r2_hidden('#skF_8', '#skF_6') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_2089, c_1187])).
% 5.05/1.88  tff(c_2102, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_75, c_32, c_76, c_817, c_2094])).
% 5.05/1.88  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.05/1.88  
% 5.05/1.88  Inference rules
% 5.05/1.88  ----------------------
% 5.05/1.88  #Ref     : 0
% 5.05/1.88  #Sup     : 382
% 5.05/1.88  #Fact    : 0
% 5.05/1.88  #Define  : 0
% 5.05/1.88  #Split   : 8
% 5.05/1.88  #Chain   : 0
% 5.05/1.88  #Close   : 0
% 5.05/1.88  
% 5.05/1.88  Ordering : KBO
% 5.05/1.88  
% 5.05/1.88  Simplification rules
% 5.05/1.88  ----------------------
% 5.05/1.88  #Subsume      : 141
% 5.05/1.88  #Demod        : 583
% 5.05/1.88  #Tautology    : 95
% 5.05/1.88  #SimpNegUnit  : 40
% 5.05/1.88  #BackRed      : 4
% 5.05/1.88  
% 5.05/1.88  #Partial instantiations: 0
% 5.05/1.88  #Strategies tried      : 1
% 5.05/1.88  
% 5.05/1.88  Timing (in seconds)
% 5.05/1.88  ----------------------
% 5.05/1.88  Preprocessing        : 0.41
% 5.05/1.88  Parsing              : 0.21
% 5.05/1.88  CNF conversion       : 0.06
% 5.05/1.88  Main loop            : 0.68
% 5.05/1.88  Inferencing          : 0.22
% 5.05/1.89  Reduction            : 0.24
% 5.05/1.89  Demodulation         : 0.18
% 5.05/1.89  BG Simplification    : 0.03
% 5.05/1.89  Subsumption          : 0.14
% 5.05/1.89  Abstraction          : 0.03
% 5.05/1.89  MUC search           : 0.00
% 5.05/1.89  Cooper               : 0.00
% 5.05/1.89  Total                : 1.15
% 5.05/1.89  Index Insertion      : 0.00
% 5.05/1.89  Index Deletion       : 0.00
% 5.05/1.89  Index Matching       : 0.00
% 5.05/1.89  BG Taut test         : 0.00
%------------------------------------------------------------------------------
