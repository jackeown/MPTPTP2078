%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:25 EST 2020

% Result     : Theorem 5.96s
% Output     : CNFRefutation 6.34s
% Verified   : 
% Statistics : Number of formulae       :  161 ( 826 expanded)
%              Number of leaves         :   38 ( 331 expanded)
%              Depth                    :   19
%              Number of atoms          :  566 (7479 expanded)
%              Number of equality atoms :   32 ( 341 expanded)
%              Maximal formula depth    :   26 (   5 average)
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

tff(f_259,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_tmap_1)).

tff(f_57,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_140,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_50,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_133,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tmap_1)).

tff(f_101,axiom,(
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

tff(f_189,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_tmap_1)).

tff(f_74,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_tops_2)).

tff(c_28,plain,(
    '#skF_7' = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_259])).

tff(c_38,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_259])).

tff(c_79,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_38])).

tff(c_36,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_259])).

tff(c_32,plain,(
    r2_hidden('#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_259])).

tff(c_80,plain,(
    r2_hidden('#skF_8','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_32])).

tff(c_58,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_259])).

tff(c_50,plain,(
    m1_pre_topc('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_259])).

tff(c_86,plain,(
    ! [B_462,A_463] :
      ( l1_pre_topc(B_462)
      | ~ m1_pre_topc(B_462,A_463)
      | ~ l1_pre_topc(A_463) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_95,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_86])).

tff(c_102,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_95])).

tff(c_42,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_259])).

tff(c_30,plain,(
    r1_tarski('#skF_6',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_259])).

tff(c_196,plain,(
    ! [B_482,A_483] :
      ( m1_subset_1(u1_struct_0(B_482),k1_zfmisc_1(u1_struct_0(A_483)))
      | ~ m1_pre_topc(B_482,A_483)
      | ~ l1_pre_topc(A_483) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_4,plain,(
    ! [A_4,B_5] :
      ( r1_tarski(A_4,B_5)
      | ~ m1_subset_1(A_4,k1_zfmisc_1(B_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_204,plain,(
    ! [B_484,A_485] :
      ( r1_tarski(u1_struct_0(B_484),u1_struct_0(A_485))
      | ~ m1_pre_topc(B_484,A_485)
      | ~ l1_pre_topc(A_485) ) ),
    inference(resolution,[status(thm)],[c_196,c_4])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(B_2,C_3)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_295,plain,(
    ! [A_500,A_501,B_502] :
      ( r1_tarski(A_500,u1_struct_0(A_501))
      | ~ r1_tarski(A_500,u1_struct_0(B_502))
      | ~ m1_pre_topc(B_502,A_501)
      | ~ l1_pre_topc(A_501) ) ),
    inference(resolution,[status(thm)],[c_204,c_2])).

tff(c_310,plain,(
    ! [A_501] :
      ( r1_tarski('#skF_6',u1_struct_0(A_501))
      | ~ m1_pre_topc('#skF_3',A_501)
      | ~ l1_pre_topc(A_501) ) ),
    inference(resolution,[status(thm)],[c_30,c_295])).

tff(c_6,plain,(
    ! [A_4,B_5] :
      ( m1_subset_1(A_4,k1_zfmisc_1(B_5))
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_68,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_259])).

tff(c_52,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_259])).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_259])).

tff(c_70,plain,
    ( ~ r1_tmap_1('#skF_3','#skF_1',k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5'),'#skF_8')
    | ~ r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_259])).

tff(c_78,plain,
    ( ~ r1_tmap_1('#skF_3','#skF_1',k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5'),'#skF_8')
    | ~ r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_70])).

tff(c_118,plain,(
    ~ r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_78])).

tff(c_66,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_259])).

tff(c_64,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_259])).

tff(c_60,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_259])).

tff(c_137,plain,(
    ! [B_471,A_472] :
      ( v2_pre_topc(B_471)
      | ~ m1_pre_topc(B_471,A_472)
      | ~ l1_pre_topc(A_472)
      | ~ v2_pre_topc(A_472) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_146,plain,
    ( v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_137])).

tff(c_155,plain,(
    v2_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_146])).

tff(c_48,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_259])).

tff(c_46,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_259])).

tff(c_44,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_259])).

tff(c_62,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_259])).

tff(c_54,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_259])).

tff(c_485,plain,(
    ! [C_529,D_525,A_527,E_526,B_528] :
      ( k3_tmap_1(A_527,B_528,C_529,D_525,E_526) = k2_partfun1(u1_struct_0(C_529),u1_struct_0(B_528),E_526,u1_struct_0(D_525))
      | ~ m1_pre_topc(D_525,C_529)
      | ~ m1_subset_1(E_526,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_529),u1_struct_0(B_528))))
      | ~ v1_funct_2(E_526,u1_struct_0(C_529),u1_struct_0(B_528))
      | ~ v1_funct_1(E_526)
      | ~ m1_pre_topc(D_525,A_527)
      | ~ m1_pre_topc(C_529,A_527)
      | ~ l1_pre_topc(B_528)
      | ~ v2_pre_topc(B_528)
      | v2_struct_0(B_528)
      | ~ l1_pre_topc(A_527)
      | ~ v2_pre_topc(A_527)
      | v2_struct_0(A_527) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_487,plain,(
    ! [A_527,D_525] :
      ( k3_tmap_1(A_527,'#skF_1','#skF_4',D_525,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0(D_525))
      | ~ m1_pre_topc(D_525,'#skF_4')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_525,A_527)
      | ~ m1_pre_topc('#skF_4',A_527)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1')
      | ~ l1_pre_topc(A_527)
      | ~ v2_pre_topc(A_527)
      | v2_struct_0(A_527) ) ),
    inference(resolution,[status(thm)],[c_44,c_485])).

tff(c_493,plain,(
    ! [A_527,D_525] :
      ( k3_tmap_1(A_527,'#skF_1','#skF_4',D_525,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0(D_525))
      | ~ m1_pre_topc(D_525,'#skF_4')
      | ~ m1_pre_topc(D_525,A_527)
      | ~ m1_pre_topc('#skF_4',A_527)
      | v2_struct_0('#skF_1')
      | ~ l1_pre_topc(A_527)
      | ~ v2_pre_topc(A_527)
      | v2_struct_0(A_527) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_48,c_46,c_487])).

tff(c_518,plain,(
    ! [A_534,D_535] :
      ( k3_tmap_1(A_534,'#skF_1','#skF_4',D_535,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0(D_535))
      | ~ m1_pre_topc(D_535,'#skF_4')
      | ~ m1_pre_topc(D_535,A_534)
      | ~ m1_pre_topc('#skF_4',A_534)
      | ~ l1_pre_topc(A_534)
      | ~ v2_pre_topc(A_534)
      | v2_struct_0(A_534) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_493])).

tff(c_522,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_518])).

tff(c_532,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_50,c_42,c_522])).

tff(c_533,plain,(
    k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_532])).

tff(c_436,plain,(
    ! [A_516,B_517,C_518,D_519] :
      ( k2_partfun1(u1_struct_0(A_516),u1_struct_0(B_517),C_518,u1_struct_0(D_519)) = k2_tmap_1(A_516,B_517,C_518,D_519)
      | ~ m1_pre_topc(D_519,A_516)
      | ~ m1_subset_1(C_518,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_516),u1_struct_0(B_517))))
      | ~ v1_funct_2(C_518,u1_struct_0(A_516),u1_struct_0(B_517))
      | ~ v1_funct_1(C_518)
      | ~ l1_pre_topc(B_517)
      | ~ v2_pre_topc(B_517)
      | v2_struct_0(B_517)
      | ~ l1_pre_topc(A_516)
      | ~ v2_pre_topc(A_516)
      | v2_struct_0(A_516) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_438,plain,(
    ! [D_519] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0(D_519)) = k2_tmap_1('#skF_4','#skF_1','#skF_5',D_519)
      | ~ m1_pre_topc(D_519,'#skF_4')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_44,c_436])).

tff(c_444,plain,(
    ! [D_519] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0(D_519)) = k2_tmap_1('#skF_4','#skF_1','#skF_5',D_519)
      | ~ m1_pre_topc(D_519,'#skF_4')
      | v2_struct_0('#skF_1')
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_102,c_66,c_64,c_48,c_46,c_438])).

tff(c_445,plain,(
    ! [D_519] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0(D_519)) = k2_tmap_1('#skF_4','#skF_1','#skF_5',D_519)
      | ~ m1_pre_topc(D_519,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_68,c_444])).

tff(c_546,plain,
    ( k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5') = k2_tmap_1('#skF_4','#skF_1','#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_533,c_445])).

tff(c_553,plain,(
    k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5') = k2_tmap_1('#skF_4','#skF_1','#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_546])).

tff(c_76,plain,
    ( r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_7')
    | r1_tmap_1('#skF_3','#skF_1',k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_259])).

tff(c_77,plain,
    ( r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_8')
    | r1_tmap_1('#skF_3','#skF_1',k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_76])).

tff(c_241,plain,(
    r1_tmap_1('#skF_3','#skF_1',k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5'),'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_118,c_77])).

tff(c_558,plain,(
    r1_tmap_1('#skF_3','#skF_1',k2_tmap_1('#skF_4','#skF_1','#skF_5','#skF_3'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_553,c_241])).

tff(c_563,plain,(
    ! [G_537,A_540,D_536,E_541,B_539,C_538] :
      ( r1_tmap_1(B_539,A_540,C_538,G_537)
      | ~ r1_tmap_1(D_536,A_540,k2_tmap_1(B_539,A_540,C_538,D_536),G_537)
      | ~ r1_tarski(E_541,u1_struct_0(D_536))
      | ~ r2_hidden(G_537,E_541)
      | ~ v3_pre_topc(E_541,B_539)
      | ~ m1_subset_1(G_537,u1_struct_0(D_536))
      | ~ m1_subset_1(G_537,u1_struct_0(B_539))
      | ~ m1_subset_1(E_541,k1_zfmisc_1(u1_struct_0(B_539)))
      | ~ m1_pre_topc(D_536,B_539)
      | v2_struct_0(D_536)
      | ~ m1_subset_1(C_538,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_539),u1_struct_0(A_540))))
      | ~ v1_funct_2(C_538,u1_struct_0(B_539),u1_struct_0(A_540))
      | ~ v1_funct_1(C_538)
      | ~ l1_pre_topc(B_539)
      | ~ v2_pre_topc(B_539)
      | v2_struct_0(B_539)
      | ~ l1_pre_topc(A_540)
      | ~ v2_pre_topc(A_540)
      | v2_struct_0(A_540) ) ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_565,plain,(
    ! [E_541] :
      ( r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_8')
      | ~ r1_tarski(E_541,u1_struct_0('#skF_3'))
      | ~ r2_hidden('#skF_8',E_541)
      | ~ v3_pre_topc(E_541,'#skF_4')
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
      | ~ m1_subset_1(E_541,k1_zfmisc_1(u1_struct_0('#skF_4')))
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
    inference(resolution,[status(thm)],[c_558,c_563])).

tff(c_568,plain,(
    ! [E_541] :
      ( r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_8')
      | ~ r1_tarski(E_541,u1_struct_0('#skF_3'))
      | ~ r2_hidden('#skF_8',E_541)
      | ~ v3_pre_topc(E_541,'#skF_4')
      | ~ m1_subset_1(E_541,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_155,c_102,c_48,c_46,c_44,c_42,c_79,c_36,c_565])).

tff(c_587,plain,(
    ! [E_542] :
      ( ~ r1_tarski(E_542,u1_struct_0('#skF_3'))
      | ~ r2_hidden('#skF_8',E_542)
      | ~ v3_pre_topc(E_542,'#skF_4')
      | ~ m1_subset_1(E_542,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_52,c_56,c_118,c_568])).

tff(c_600,plain,(
    ! [A_543] :
      ( ~ r1_tarski(A_543,u1_struct_0('#skF_3'))
      | ~ r2_hidden('#skF_8',A_543)
      | ~ v3_pre_topc(A_543,'#skF_4')
      | ~ r1_tarski(A_543,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_6,c_587])).

tff(c_626,plain,
    ( ~ r2_hidden('#skF_8','#skF_6')
    | ~ v3_pre_topc('#skF_6','#skF_4')
    | ~ r1_tarski('#skF_6',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_30,c_600])).

tff(c_645,plain,
    ( ~ v3_pre_topc('#skF_6','#skF_4')
    | ~ r1_tarski('#skF_6',u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_626])).

tff(c_646,plain,(
    ~ r1_tarski('#skF_6',u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_645])).

tff(c_655,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_310,c_646])).

tff(c_668,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_42,c_655])).

tff(c_669,plain,(
    ~ v3_pre_topc('#skF_6','#skF_4') ),
    inference(splitRight,[status(thm)],[c_645])).

tff(c_670,plain,(
    r1_tarski('#skF_6',u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_645])).

tff(c_34,plain,(
    v3_pre_topc('#skF_6','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_259])).

tff(c_40,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_259])).

tff(c_350,plain,(
    ! [D_506,C_507,A_508] :
      ( v3_pre_topc(D_506,C_507)
      | ~ m1_subset_1(D_506,k1_zfmisc_1(u1_struct_0(C_507)))
      | ~ v3_pre_topc(D_506,A_508)
      | ~ m1_pre_topc(C_507,A_508)
      | ~ m1_subset_1(D_506,k1_zfmisc_1(u1_struct_0(A_508)))
      | ~ l1_pre_topc(A_508) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_845,plain,(
    ! [A_555,C_556,A_557] :
      ( v3_pre_topc(A_555,C_556)
      | ~ v3_pre_topc(A_555,A_557)
      | ~ m1_pre_topc(C_556,A_557)
      | ~ m1_subset_1(A_555,k1_zfmisc_1(u1_struct_0(A_557)))
      | ~ l1_pre_topc(A_557)
      | ~ r1_tarski(A_555,u1_struct_0(C_556)) ) ),
    inference(resolution,[status(thm)],[c_6,c_350])).

tff(c_853,plain,(
    ! [A_555] :
      ( v3_pre_topc(A_555,'#skF_4')
      | ~ v3_pre_topc(A_555,'#skF_2')
      | ~ m1_subset_1(A_555,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ r1_tarski(A_555,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_50,c_845])).

tff(c_1003,plain,(
    ! [A_569] :
      ( v3_pre_topc(A_569,'#skF_4')
      | ~ v3_pre_topc(A_569,'#skF_2')
      | ~ m1_subset_1(A_569,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ r1_tarski(A_569,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_853])).

tff(c_1014,plain,
    ( v3_pre_topc('#skF_6','#skF_4')
    | ~ v3_pre_topc('#skF_6','#skF_2')
    | ~ r1_tarski('#skF_6',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_40,c_1003])).

tff(c_1021,plain,(
    v3_pre_topc('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_670,c_34,c_1014])).

tff(c_1023,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_669,c_1021])).

tff(c_1025,plain,(
    r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_8') ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_1145,plain,(
    ! [B_592,A_593] :
      ( m1_subset_1(u1_struct_0(B_592),k1_zfmisc_1(u1_struct_0(A_593)))
      | ~ m1_pre_topc(B_592,A_593)
      | ~ l1_pre_topc(A_593) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_1164,plain,(
    ! [B_596,A_597] :
      ( r1_tarski(u1_struct_0(B_596),u1_struct_0(A_597))
      | ~ m1_pre_topc(B_596,A_597)
      | ~ l1_pre_topc(A_597) ) ),
    inference(resolution,[status(thm)],[c_1145,c_4])).

tff(c_1245,plain,(
    ! [A_611,A_612,B_613] :
      ( r1_tarski(A_611,u1_struct_0(A_612))
      | ~ r1_tarski(A_611,u1_struct_0(B_613))
      | ~ m1_pre_topc(B_613,A_612)
      | ~ l1_pre_topc(A_612) ) ),
    inference(resolution,[status(thm)],[c_1164,c_2])).

tff(c_1260,plain,(
    ! [A_612] :
      ( r1_tarski('#skF_6',u1_struct_0(A_612))
      | ~ m1_pre_topc('#skF_3',A_612)
      | ~ l1_pre_topc(A_612) ) ),
    inference(resolution,[status(thm)],[c_30,c_1245])).

tff(c_1070,plain,(
    ! [B_577,A_578] :
      ( v2_pre_topc(B_577)
      | ~ m1_pre_topc(B_577,A_578)
      | ~ l1_pre_topc(A_578)
      | ~ v2_pre_topc(A_578) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1079,plain,
    ( v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_1070])).

tff(c_1088,plain,(
    v2_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_1079])).

tff(c_1507,plain,(
    ! [E_648,G_644,C_645,A_647,D_643,B_646] :
      ( r1_tmap_1(D_643,A_647,k2_tmap_1(B_646,A_647,C_645,D_643),G_644)
      | ~ r1_tmap_1(B_646,A_647,C_645,G_644)
      | ~ r1_tarski(E_648,u1_struct_0(D_643))
      | ~ r2_hidden(G_644,E_648)
      | ~ v3_pre_topc(E_648,B_646)
      | ~ m1_subset_1(G_644,u1_struct_0(D_643))
      | ~ m1_subset_1(G_644,u1_struct_0(B_646))
      | ~ m1_subset_1(E_648,k1_zfmisc_1(u1_struct_0(B_646)))
      | ~ m1_pre_topc(D_643,B_646)
      | v2_struct_0(D_643)
      | ~ m1_subset_1(C_645,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_646),u1_struct_0(A_647))))
      | ~ v1_funct_2(C_645,u1_struct_0(B_646),u1_struct_0(A_647))
      | ~ v1_funct_1(C_645)
      | ~ l1_pre_topc(B_646)
      | ~ v2_pre_topc(B_646)
      | v2_struct_0(B_646)
      | ~ l1_pre_topc(A_647)
      | ~ v2_pre_topc(A_647)
      | v2_struct_0(A_647) ) ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_1525,plain,(
    ! [A_647,B_646,C_645,G_644] :
      ( r1_tmap_1('#skF_3',A_647,k2_tmap_1(B_646,A_647,C_645,'#skF_3'),G_644)
      | ~ r1_tmap_1(B_646,A_647,C_645,G_644)
      | ~ r2_hidden(G_644,'#skF_6')
      | ~ v3_pre_topc('#skF_6',B_646)
      | ~ m1_subset_1(G_644,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(G_644,u1_struct_0(B_646))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0(B_646)))
      | ~ m1_pre_topc('#skF_3',B_646)
      | v2_struct_0('#skF_3')
      | ~ m1_subset_1(C_645,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_646),u1_struct_0(A_647))))
      | ~ v1_funct_2(C_645,u1_struct_0(B_646),u1_struct_0(A_647))
      | ~ v1_funct_1(C_645)
      | ~ l1_pre_topc(B_646)
      | ~ v2_pre_topc(B_646)
      | v2_struct_0(B_646)
      | ~ l1_pre_topc(A_647)
      | ~ v2_pre_topc(A_647)
      | v2_struct_0(A_647) ) ),
    inference(resolution,[status(thm)],[c_30,c_1507])).

tff(c_1796,plain,(
    ! [A_674,B_675,C_676,G_677] :
      ( r1_tmap_1('#skF_3',A_674,k2_tmap_1(B_675,A_674,C_676,'#skF_3'),G_677)
      | ~ r1_tmap_1(B_675,A_674,C_676,G_677)
      | ~ r2_hidden(G_677,'#skF_6')
      | ~ v3_pre_topc('#skF_6',B_675)
      | ~ m1_subset_1(G_677,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(G_677,u1_struct_0(B_675))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0(B_675)))
      | ~ m1_pre_topc('#skF_3',B_675)
      | ~ m1_subset_1(C_676,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_675),u1_struct_0(A_674))))
      | ~ v1_funct_2(C_676,u1_struct_0(B_675),u1_struct_0(A_674))
      | ~ v1_funct_1(C_676)
      | ~ l1_pre_topc(B_675)
      | ~ v2_pre_topc(B_675)
      | v2_struct_0(B_675)
      | ~ l1_pre_topc(A_674)
      | ~ v2_pre_topc(A_674)
      | v2_struct_0(A_674) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_1525])).

tff(c_1798,plain,(
    ! [G_677] :
      ( r1_tmap_1('#skF_3','#skF_1',k2_tmap_1('#skF_4','#skF_1','#skF_5','#skF_3'),G_677)
      | ~ r1_tmap_1('#skF_4','#skF_1','#skF_5',G_677)
      | ~ r2_hidden(G_677,'#skF_6')
      | ~ v3_pre_topc('#skF_6','#skF_4')
      | ~ m1_subset_1(G_677,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(G_677,u1_struct_0('#skF_4'))
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
    inference(resolution,[status(thm)],[c_44,c_1796])).

tff(c_1804,plain,(
    ! [G_677] :
      ( r1_tmap_1('#skF_3','#skF_1',k2_tmap_1('#skF_4','#skF_1','#skF_5','#skF_3'),G_677)
      | ~ r1_tmap_1('#skF_4','#skF_1','#skF_5',G_677)
      | ~ r2_hidden(G_677,'#skF_6')
      | ~ v3_pre_topc('#skF_6','#skF_4')
      | ~ m1_subset_1(G_677,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(G_677,u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_1088,c_102,c_48,c_46,c_42,c_1798])).

tff(c_1805,plain,(
    ! [G_677] :
      ( r1_tmap_1('#skF_3','#skF_1',k2_tmap_1('#skF_4','#skF_1','#skF_5','#skF_3'),G_677)
      | ~ r1_tmap_1('#skF_4','#skF_1','#skF_5',G_677)
      | ~ r2_hidden(G_677,'#skF_6')
      | ~ v3_pre_topc('#skF_6','#skF_4')
      | ~ m1_subset_1(G_677,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(G_677,u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_52,c_1804])).

tff(c_1928,plain,(
    ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_1805])).

tff(c_1932,plain,(
    ~ r1_tarski('#skF_6',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_6,c_1928])).

tff(c_1941,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_1260,c_1932])).

tff(c_1954,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_42,c_1941])).

tff(c_1956,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_1805])).

tff(c_1966,plain,(
    r1_tarski('#skF_6',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_1956,c_4])).

tff(c_1280,plain,(
    ! [D_615,C_616,A_617] :
      ( v3_pre_topc(D_615,C_616)
      | ~ m1_subset_1(D_615,k1_zfmisc_1(u1_struct_0(C_616)))
      | ~ v3_pre_topc(D_615,A_617)
      | ~ m1_pre_topc(C_616,A_617)
      | ~ m1_subset_1(D_615,k1_zfmisc_1(u1_struct_0(A_617)))
      | ~ l1_pre_topc(A_617) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1776,plain,(
    ! [A_671,C_672,A_673] :
      ( v3_pre_topc(A_671,C_672)
      | ~ v3_pre_topc(A_671,A_673)
      | ~ m1_pre_topc(C_672,A_673)
      | ~ m1_subset_1(A_671,k1_zfmisc_1(u1_struct_0(A_673)))
      | ~ l1_pre_topc(A_673)
      | ~ r1_tarski(A_671,u1_struct_0(C_672)) ) ),
    inference(resolution,[status(thm)],[c_6,c_1280])).

tff(c_1784,plain,(
    ! [A_671] :
      ( v3_pre_topc(A_671,'#skF_4')
      | ~ v3_pre_topc(A_671,'#skF_2')
      | ~ m1_subset_1(A_671,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ r1_tarski(A_671,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_50,c_1776])).

tff(c_2712,plain,(
    ! [A_732] :
      ( v3_pre_topc(A_732,'#skF_4')
      | ~ v3_pre_topc(A_732,'#skF_2')
      | ~ m1_subset_1(A_732,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ r1_tarski(A_732,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_1784])).

tff(c_2723,plain,
    ( v3_pre_topc('#skF_6','#skF_4')
    | ~ v3_pre_topc('#skF_6','#skF_2')
    | ~ r1_tarski('#skF_6',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_40,c_2712])).

tff(c_2730,plain,(
    v3_pre_topc('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1966,c_34,c_2723])).

tff(c_1955,plain,(
    ! [G_677] :
      ( ~ v3_pre_topc('#skF_6','#skF_4')
      | r1_tmap_1('#skF_3','#skF_1',k2_tmap_1('#skF_4','#skF_1','#skF_5','#skF_3'),G_677)
      | ~ r1_tmap_1('#skF_4','#skF_1','#skF_5',G_677)
      | ~ r2_hidden(G_677,'#skF_6')
      | ~ m1_subset_1(G_677,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(G_677,u1_struct_0('#skF_4')) ) ),
    inference(splitRight,[status(thm)],[c_1805])).

tff(c_3929,plain,(
    ! [G_810] :
      ( r1_tmap_1('#skF_3','#skF_1',k2_tmap_1('#skF_4','#skF_1','#skF_5','#skF_3'),G_810)
      | ~ r1_tmap_1('#skF_4','#skF_1','#skF_5',G_810)
      | ~ r2_hidden(G_810,'#skF_6')
      | ~ m1_subset_1(G_810,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(G_810,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2730,c_1955])).

tff(c_1428,plain,(
    ! [B_639,C_640,A_638,D_636,E_637] :
      ( k3_tmap_1(A_638,B_639,C_640,D_636,E_637) = k2_partfun1(u1_struct_0(C_640),u1_struct_0(B_639),E_637,u1_struct_0(D_636))
      | ~ m1_pre_topc(D_636,C_640)
      | ~ m1_subset_1(E_637,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_640),u1_struct_0(B_639))))
      | ~ v1_funct_2(E_637,u1_struct_0(C_640),u1_struct_0(B_639))
      | ~ v1_funct_1(E_637)
      | ~ m1_pre_topc(D_636,A_638)
      | ~ m1_pre_topc(C_640,A_638)
      | ~ l1_pre_topc(B_639)
      | ~ v2_pre_topc(B_639)
      | v2_struct_0(B_639)
      | ~ l1_pre_topc(A_638)
      | ~ v2_pre_topc(A_638)
      | v2_struct_0(A_638) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_1430,plain,(
    ! [A_638,D_636] :
      ( k3_tmap_1(A_638,'#skF_1','#skF_4',D_636,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0(D_636))
      | ~ m1_pre_topc(D_636,'#skF_4')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_636,A_638)
      | ~ m1_pre_topc('#skF_4',A_638)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1')
      | ~ l1_pre_topc(A_638)
      | ~ v2_pre_topc(A_638)
      | v2_struct_0(A_638) ) ),
    inference(resolution,[status(thm)],[c_44,c_1428])).

tff(c_1436,plain,(
    ! [A_638,D_636] :
      ( k3_tmap_1(A_638,'#skF_1','#skF_4',D_636,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0(D_636))
      | ~ m1_pre_topc(D_636,'#skF_4')
      | ~ m1_pre_topc(D_636,A_638)
      | ~ m1_pre_topc('#skF_4',A_638)
      | v2_struct_0('#skF_1')
      | ~ l1_pre_topc(A_638)
      | ~ v2_pre_topc(A_638)
      | v2_struct_0(A_638) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_48,c_46,c_1430])).

tff(c_1446,plain,(
    ! [A_641,D_642] :
      ( k3_tmap_1(A_641,'#skF_1','#skF_4',D_642,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0(D_642))
      | ~ m1_pre_topc(D_642,'#skF_4')
      | ~ m1_pre_topc(D_642,A_641)
      | ~ m1_pre_topc('#skF_4',A_641)
      | ~ l1_pre_topc(A_641)
      | ~ v2_pre_topc(A_641)
      | v2_struct_0(A_641) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1436])).

tff(c_1450,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_1446])).

tff(c_1460,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_50,c_42,c_1450])).

tff(c_1461,plain,(
    k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_1460])).

tff(c_1385,plain,(
    ! [A_627,B_628,C_629,D_630] :
      ( k2_partfun1(u1_struct_0(A_627),u1_struct_0(B_628),C_629,u1_struct_0(D_630)) = k2_tmap_1(A_627,B_628,C_629,D_630)
      | ~ m1_pre_topc(D_630,A_627)
      | ~ m1_subset_1(C_629,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_627),u1_struct_0(B_628))))
      | ~ v1_funct_2(C_629,u1_struct_0(A_627),u1_struct_0(B_628))
      | ~ v1_funct_1(C_629)
      | ~ l1_pre_topc(B_628)
      | ~ v2_pre_topc(B_628)
      | v2_struct_0(B_628)
      | ~ l1_pre_topc(A_627)
      | ~ v2_pre_topc(A_627)
      | v2_struct_0(A_627) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_1387,plain,(
    ! [D_630] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0(D_630)) = k2_tmap_1('#skF_4','#skF_1','#skF_5',D_630)
      | ~ m1_pre_topc(D_630,'#skF_4')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_44,c_1385])).

tff(c_1393,plain,(
    ! [D_630] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0(D_630)) = k2_tmap_1('#skF_4','#skF_1','#skF_5',D_630)
      | ~ m1_pre_topc(D_630,'#skF_4')
      | v2_struct_0('#skF_1')
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1088,c_102,c_66,c_64,c_48,c_46,c_1387])).

tff(c_1394,plain,(
    ! [D_630] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0(D_630)) = k2_tmap_1('#skF_4','#skF_1','#skF_5',D_630)
      | ~ m1_pre_topc(D_630,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_68,c_1393])).

tff(c_1473,plain,
    ( k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5') = k2_tmap_1('#skF_4','#skF_1','#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1461,c_1394])).

tff(c_1480,plain,(
    k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5') = k2_tmap_1('#skF_4','#skF_1','#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_1473])).

tff(c_1024,plain,(
    ~ r1_tmap_1('#skF_3','#skF_1',k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_1026,plain,(
    r1_tmap_1('#skF_3','#skF_1',k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5'),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_77])).

tff(c_1066,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1024,c_1026])).

tff(c_1068,plain,(
    ~ r1_tmap_1('#skF_3','#skF_1',k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_77])).

tff(c_1485,plain,(
    ~ r1_tmap_1('#skF_3','#skF_1',k2_tmap_1('#skF_4','#skF_1','#skF_5','#skF_3'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1480,c_1068])).

tff(c_3934,plain,
    ( ~ r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_8')
    | ~ r2_hidden('#skF_8','#skF_6')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_3929,c_1485])).

tff(c_3942,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_36,c_80,c_1025,c_3934])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 19:43:44 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.96/2.22  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.34/2.23  
% 6.34/2.23  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.34/2.23  %$ r1_tmap_1 > v1_funct_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4
% 6.34/2.23  
% 6.34/2.23  %Foreground sorts:
% 6.34/2.23  
% 6.34/2.23  
% 6.34/2.23  %Background operators:
% 6.34/2.23  
% 6.34/2.23  
% 6.34/2.23  %Foreground operators:
% 6.34/2.23  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 6.34/2.23  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 6.34/2.23  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.34/2.23  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 6.34/2.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.34/2.23  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.34/2.23  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 6.34/2.23  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 6.34/2.23  tff('#skF_7', type, '#skF_7': $i).
% 6.34/2.23  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.34/2.23  tff('#skF_5', type, '#skF_5': $i).
% 6.34/2.23  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.34/2.23  tff('#skF_6', type, '#skF_6': $i).
% 6.34/2.23  tff('#skF_2', type, '#skF_2': $i).
% 6.34/2.23  tff('#skF_3', type, '#skF_3': $i).
% 6.34/2.23  tff('#skF_1', type, '#skF_1': $i).
% 6.34/2.23  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.34/2.23  tff('#skF_8', type, '#skF_8': $i).
% 6.34/2.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.34/2.23  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.34/2.23  tff('#skF_4', type, '#skF_4': $i).
% 6.34/2.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.34/2.23  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 6.34/2.23  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 6.34/2.23  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 6.34/2.23  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 6.34/2.23  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 6.34/2.23  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.34/2.23  
% 6.34/2.26  tff(f_259, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, B)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(A))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(A))))) => (m1_pre_topc(C, D) => (![F]: (m1_subset_1(F, k1_zfmisc_1(u1_struct_0(B))) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (![H]: (m1_subset_1(H, u1_struct_0(C)) => ((((v3_pre_topc(F, B) & r2_hidden(G, F)) & r1_tarski(F, u1_struct_0(C))) & (G = H)) => (r1_tmap_1(D, A, E, G) <=> r1_tmap_1(C, A, k3_tmap_1(B, A, D, C, E), H)))))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_tmap_1)).
% 6.34/2.26  tff(f_57, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 6.34/2.26  tff(f_140, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 6.34/2.26  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 6.34/2.26  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 6.34/2.26  tff(f_50, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_pre_topc)).
% 6.34/2.26  tff(f_133, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (m1_pre_topc(C, A) => (![D]: (m1_pre_topc(D, A) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (m1_pre_topc(D, C) => (k3_tmap_1(A, B, C, D, E) = k2_partfun1(u1_struct_0(C), u1_struct_0(B), E, u1_struct_0(D)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tmap_1)).
% 6.34/2.26  tff(f_101, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tmap_1)).
% 6.34/2.26  tff(f_189, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(B))) => (![F]: (m1_subset_1(F, u1_struct_0(B)) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => ((((v3_pre_topc(E, B) & r2_hidden(F, E)) & r1_tarski(E, u1_struct_0(D))) & (F = G)) => (r1_tmap_1(B, A, C, F) <=> r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), G))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_tmap_1)).
% 6.34/2.26  tff(f_74, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_pre_topc(C, A) => (v3_pre_topc(B, A) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(C))) => ((D = B) => v3_pre_topc(D, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_tops_2)).
% 6.34/2.26  tff(c_28, plain, ('#skF_7'='#skF_8'), inference(cnfTransformation, [status(thm)], [f_259])).
% 6.34/2.26  tff(c_38, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_259])).
% 6.34/2.26  tff(c_79, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_38])).
% 6.34/2.26  tff(c_36, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_259])).
% 6.34/2.26  tff(c_32, plain, (r2_hidden('#skF_7', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_259])).
% 6.34/2.26  tff(c_80, plain, (r2_hidden('#skF_8', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_32])).
% 6.34/2.26  tff(c_58, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_259])).
% 6.34/2.26  tff(c_50, plain, (m1_pre_topc('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_259])).
% 6.34/2.26  tff(c_86, plain, (![B_462, A_463]: (l1_pre_topc(B_462) | ~m1_pre_topc(B_462, A_463) | ~l1_pre_topc(A_463))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.34/2.26  tff(c_95, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_50, c_86])).
% 6.34/2.26  tff(c_102, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_95])).
% 6.34/2.26  tff(c_42, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_259])).
% 6.34/2.26  tff(c_30, plain, (r1_tarski('#skF_6', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_259])).
% 6.34/2.26  tff(c_196, plain, (![B_482, A_483]: (m1_subset_1(u1_struct_0(B_482), k1_zfmisc_1(u1_struct_0(A_483))) | ~m1_pre_topc(B_482, A_483) | ~l1_pre_topc(A_483))), inference(cnfTransformation, [status(thm)], [f_140])).
% 6.34/2.26  tff(c_4, plain, (![A_4, B_5]: (r1_tarski(A_4, B_5) | ~m1_subset_1(A_4, k1_zfmisc_1(B_5)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.34/2.26  tff(c_204, plain, (![B_484, A_485]: (r1_tarski(u1_struct_0(B_484), u1_struct_0(A_485)) | ~m1_pre_topc(B_484, A_485) | ~l1_pre_topc(A_485))), inference(resolution, [status(thm)], [c_196, c_4])).
% 6.34/2.26  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(B_2, C_3) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.34/2.26  tff(c_295, plain, (![A_500, A_501, B_502]: (r1_tarski(A_500, u1_struct_0(A_501)) | ~r1_tarski(A_500, u1_struct_0(B_502)) | ~m1_pre_topc(B_502, A_501) | ~l1_pre_topc(A_501))), inference(resolution, [status(thm)], [c_204, c_2])).
% 6.34/2.26  tff(c_310, plain, (![A_501]: (r1_tarski('#skF_6', u1_struct_0(A_501)) | ~m1_pre_topc('#skF_3', A_501) | ~l1_pre_topc(A_501))), inference(resolution, [status(thm)], [c_30, c_295])).
% 6.34/2.26  tff(c_6, plain, (![A_4, B_5]: (m1_subset_1(A_4, k1_zfmisc_1(B_5)) | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.34/2.26  tff(c_68, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_259])).
% 6.34/2.26  tff(c_52, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_259])).
% 6.34/2.26  tff(c_56, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_259])).
% 6.34/2.26  tff(c_70, plain, (~r1_tmap_1('#skF_3', '#skF_1', k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5'), '#skF_8') | ~r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_259])).
% 6.34/2.26  tff(c_78, plain, (~r1_tmap_1('#skF_3', '#skF_1', k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5'), '#skF_8') | ~r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_70])).
% 6.34/2.26  tff(c_118, plain, (~r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_8')), inference(splitLeft, [status(thm)], [c_78])).
% 6.34/2.26  tff(c_66, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_259])).
% 6.34/2.26  tff(c_64, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_259])).
% 6.34/2.26  tff(c_60, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_259])).
% 6.34/2.26  tff(c_137, plain, (![B_471, A_472]: (v2_pre_topc(B_471) | ~m1_pre_topc(B_471, A_472) | ~l1_pre_topc(A_472) | ~v2_pre_topc(A_472))), inference(cnfTransformation, [status(thm)], [f_50])).
% 6.34/2.26  tff(c_146, plain, (v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_50, c_137])).
% 6.34/2.26  tff(c_155, plain, (v2_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_146])).
% 6.34/2.26  tff(c_48, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_259])).
% 6.34/2.26  tff(c_46, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_259])).
% 6.34/2.26  tff(c_44, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_259])).
% 6.34/2.26  tff(c_62, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_259])).
% 6.34/2.26  tff(c_54, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_259])).
% 6.34/2.26  tff(c_485, plain, (![C_529, D_525, A_527, E_526, B_528]: (k3_tmap_1(A_527, B_528, C_529, D_525, E_526)=k2_partfun1(u1_struct_0(C_529), u1_struct_0(B_528), E_526, u1_struct_0(D_525)) | ~m1_pre_topc(D_525, C_529) | ~m1_subset_1(E_526, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_529), u1_struct_0(B_528)))) | ~v1_funct_2(E_526, u1_struct_0(C_529), u1_struct_0(B_528)) | ~v1_funct_1(E_526) | ~m1_pre_topc(D_525, A_527) | ~m1_pre_topc(C_529, A_527) | ~l1_pre_topc(B_528) | ~v2_pre_topc(B_528) | v2_struct_0(B_528) | ~l1_pre_topc(A_527) | ~v2_pre_topc(A_527) | v2_struct_0(A_527))), inference(cnfTransformation, [status(thm)], [f_133])).
% 6.34/2.26  tff(c_487, plain, (![A_527, D_525]: (k3_tmap_1(A_527, '#skF_1', '#skF_4', D_525, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0(D_525)) | ~m1_pre_topc(D_525, '#skF_4') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_525, A_527) | ~m1_pre_topc('#skF_4', A_527) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~l1_pre_topc(A_527) | ~v2_pre_topc(A_527) | v2_struct_0(A_527))), inference(resolution, [status(thm)], [c_44, c_485])).
% 6.34/2.26  tff(c_493, plain, (![A_527, D_525]: (k3_tmap_1(A_527, '#skF_1', '#skF_4', D_525, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0(D_525)) | ~m1_pre_topc(D_525, '#skF_4') | ~m1_pre_topc(D_525, A_527) | ~m1_pre_topc('#skF_4', A_527) | v2_struct_0('#skF_1') | ~l1_pre_topc(A_527) | ~v2_pre_topc(A_527) | v2_struct_0(A_527))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_48, c_46, c_487])).
% 6.34/2.26  tff(c_518, plain, (![A_534, D_535]: (k3_tmap_1(A_534, '#skF_1', '#skF_4', D_535, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0(D_535)) | ~m1_pre_topc(D_535, '#skF_4') | ~m1_pre_topc(D_535, A_534) | ~m1_pre_topc('#skF_4', A_534) | ~l1_pre_topc(A_534) | ~v2_pre_topc(A_534) | v2_struct_0(A_534))), inference(negUnitSimplification, [status(thm)], [c_68, c_493])).
% 6.34/2.26  tff(c_522, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5') | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_54, c_518])).
% 6.34/2.26  tff(c_532, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_50, c_42, c_522])).
% 6.34/2.26  tff(c_533, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_62, c_532])).
% 6.34/2.26  tff(c_436, plain, (![A_516, B_517, C_518, D_519]: (k2_partfun1(u1_struct_0(A_516), u1_struct_0(B_517), C_518, u1_struct_0(D_519))=k2_tmap_1(A_516, B_517, C_518, D_519) | ~m1_pre_topc(D_519, A_516) | ~m1_subset_1(C_518, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_516), u1_struct_0(B_517)))) | ~v1_funct_2(C_518, u1_struct_0(A_516), u1_struct_0(B_517)) | ~v1_funct_1(C_518) | ~l1_pre_topc(B_517) | ~v2_pre_topc(B_517) | v2_struct_0(B_517) | ~l1_pre_topc(A_516) | ~v2_pre_topc(A_516) | v2_struct_0(A_516))), inference(cnfTransformation, [status(thm)], [f_101])).
% 6.34/2.26  tff(c_438, plain, (![D_519]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0(D_519))=k2_tmap_1('#skF_4', '#skF_1', '#skF_5', D_519) | ~m1_pre_topc(D_519, '#skF_4') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_44, c_436])).
% 6.34/2.26  tff(c_444, plain, (![D_519]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0(D_519))=k2_tmap_1('#skF_4', '#skF_1', '#skF_5', D_519) | ~m1_pre_topc(D_519, '#skF_4') | v2_struct_0('#skF_1') | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_155, c_102, c_66, c_64, c_48, c_46, c_438])).
% 6.34/2.26  tff(c_445, plain, (![D_519]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0(D_519))=k2_tmap_1('#skF_4', '#skF_1', '#skF_5', D_519) | ~m1_pre_topc(D_519, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_52, c_68, c_444])).
% 6.34/2.26  tff(c_546, plain, (k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5')=k2_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_533, c_445])).
% 6.34/2.26  tff(c_553, plain, (k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5')=k2_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_546])).
% 6.34/2.26  tff(c_76, plain, (r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_7') | r1_tmap_1('#skF_3', '#skF_1', k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_259])).
% 6.34/2.26  tff(c_77, plain, (r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_8') | r1_tmap_1('#skF_3', '#skF_1', k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_76])).
% 6.34/2.26  tff(c_241, plain, (r1_tmap_1('#skF_3', '#skF_1', k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5'), '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_118, c_77])).
% 6.34/2.26  tff(c_558, plain, (r1_tmap_1('#skF_3', '#skF_1', k2_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_3'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_553, c_241])).
% 6.34/2.26  tff(c_563, plain, (![G_537, A_540, D_536, E_541, B_539, C_538]: (r1_tmap_1(B_539, A_540, C_538, G_537) | ~r1_tmap_1(D_536, A_540, k2_tmap_1(B_539, A_540, C_538, D_536), G_537) | ~r1_tarski(E_541, u1_struct_0(D_536)) | ~r2_hidden(G_537, E_541) | ~v3_pre_topc(E_541, B_539) | ~m1_subset_1(G_537, u1_struct_0(D_536)) | ~m1_subset_1(G_537, u1_struct_0(B_539)) | ~m1_subset_1(E_541, k1_zfmisc_1(u1_struct_0(B_539))) | ~m1_pre_topc(D_536, B_539) | v2_struct_0(D_536) | ~m1_subset_1(C_538, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_539), u1_struct_0(A_540)))) | ~v1_funct_2(C_538, u1_struct_0(B_539), u1_struct_0(A_540)) | ~v1_funct_1(C_538) | ~l1_pre_topc(B_539) | ~v2_pre_topc(B_539) | v2_struct_0(B_539) | ~l1_pre_topc(A_540) | ~v2_pre_topc(A_540) | v2_struct_0(A_540))), inference(cnfTransformation, [status(thm)], [f_189])).
% 6.34/2.26  tff(c_565, plain, (![E_541]: (r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_8') | ~r1_tarski(E_541, u1_struct_0('#skF_3')) | ~r2_hidden('#skF_8', E_541) | ~v3_pre_topc(E_541, '#skF_4') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~m1_subset_1(E_541, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_pre_topc('#skF_3', '#skF_4') | v2_struct_0('#skF_3') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_558, c_563])).
% 6.34/2.26  tff(c_568, plain, (![E_541]: (r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_8') | ~r1_tarski(E_541, u1_struct_0('#skF_3')) | ~r2_hidden('#skF_8', E_541) | ~v3_pre_topc(E_541, '#skF_4') | ~m1_subset_1(E_541, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_struct_0('#skF_3') | v2_struct_0('#skF_4') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_155, c_102, c_48, c_46, c_44, c_42, c_79, c_36, c_565])).
% 6.34/2.26  tff(c_587, plain, (![E_542]: (~r1_tarski(E_542, u1_struct_0('#skF_3')) | ~r2_hidden('#skF_8', E_542) | ~v3_pre_topc(E_542, '#skF_4') | ~m1_subset_1(E_542, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_68, c_52, c_56, c_118, c_568])).
% 6.34/2.26  tff(c_600, plain, (![A_543]: (~r1_tarski(A_543, u1_struct_0('#skF_3')) | ~r2_hidden('#skF_8', A_543) | ~v3_pre_topc(A_543, '#skF_4') | ~r1_tarski(A_543, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_6, c_587])).
% 6.34/2.26  tff(c_626, plain, (~r2_hidden('#skF_8', '#skF_6') | ~v3_pre_topc('#skF_6', '#skF_4') | ~r1_tarski('#skF_6', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_30, c_600])).
% 6.34/2.26  tff(c_645, plain, (~v3_pre_topc('#skF_6', '#skF_4') | ~r1_tarski('#skF_6', u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_626])).
% 6.34/2.26  tff(c_646, plain, (~r1_tarski('#skF_6', u1_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_645])).
% 6.34/2.26  tff(c_655, plain, (~m1_pre_topc('#skF_3', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_310, c_646])).
% 6.34/2.26  tff(c_668, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_102, c_42, c_655])).
% 6.34/2.26  tff(c_669, plain, (~v3_pre_topc('#skF_6', '#skF_4')), inference(splitRight, [status(thm)], [c_645])).
% 6.34/2.26  tff(c_670, plain, (r1_tarski('#skF_6', u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_645])).
% 6.34/2.26  tff(c_34, plain, (v3_pre_topc('#skF_6', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_259])).
% 6.34/2.26  tff(c_40, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_259])).
% 6.34/2.26  tff(c_350, plain, (![D_506, C_507, A_508]: (v3_pre_topc(D_506, C_507) | ~m1_subset_1(D_506, k1_zfmisc_1(u1_struct_0(C_507))) | ~v3_pre_topc(D_506, A_508) | ~m1_pre_topc(C_507, A_508) | ~m1_subset_1(D_506, k1_zfmisc_1(u1_struct_0(A_508))) | ~l1_pre_topc(A_508))), inference(cnfTransformation, [status(thm)], [f_74])).
% 6.34/2.26  tff(c_845, plain, (![A_555, C_556, A_557]: (v3_pre_topc(A_555, C_556) | ~v3_pre_topc(A_555, A_557) | ~m1_pre_topc(C_556, A_557) | ~m1_subset_1(A_555, k1_zfmisc_1(u1_struct_0(A_557))) | ~l1_pre_topc(A_557) | ~r1_tarski(A_555, u1_struct_0(C_556)))), inference(resolution, [status(thm)], [c_6, c_350])).
% 6.34/2.26  tff(c_853, plain, (![A_555]: (v3_pre_topc(A_555, '#skF_4') | ~v3_pre_topc(A_555, '#skF_2') | ~m1_subset_1(A_555, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~r1_tarski(A_555, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_50, c_845])).
% 6.34/2.26  tff(c_1003, plain, (![A_569]: (v3_pre_topc(A_569, '#skF_4') | ~v3_pre_topc(A_569, '#skF_2') | ~m1_subset_1(A_569, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~r1_tarski(A_569, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_853])).
% 6.34/2.26  tff(c_1014, plain, (v3_pre_topc('#skF_6', '#skF_4') | ~v3_pre_topc('#skF_6', '#skF_2') | ~r1_tarski('#skF_6', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_40, c_1003])).
% 6.34/2.26  tff(c_1021, plain, (v3_pre_topc('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_670, c_34, c_1014])).
% 6.34/2.26  tff(c_1023, plain, $false, inference(negUnitSimplification, [status(thm)], [c_669, c_1021])).
% 6.34/2.26  tff(c_1025, plain, (r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_8')), inference(splitRight, [status(thm)], [c_78])).
% 6.34/2.26  tff(c_1145, plain, (![B_592, A_593]: (m1_subset_1(u1_struct_0(B_592), k1_zfmisc_1(u1_struct_0(A_593))) | ~m1_pre_topc(B_592, A_593) | ~l1_pre_topc(A_593))), inference(cnfTransformation, [status(thm)], [f_140])).
% 6.34/2.26  tff(c_1164, plain, (![B_596, A_597]: (r1_tarski(u1_struct_0(B_596), u1_struct_0(A_597)) | ~m1_pre_topc(B_596, A_597) | ~l1_pre_topc(A_597))), inference(resolution, [status(thm)], [c_1145, c_4])).
% 6.34/2.26  tff(c_1245, plain, (![A_611, A_612, B_613]: (r1_tarski(A_611, u1_struct_0(A_612)) | ~r1_tarski(A_611, u1_struct_0(B_613)) | ~m1_pre_topc(B_613, A_612) | ~l1_pre_topc(A_612))), inference(resolution, [status(thm)], [c_1164, c_2])).
% 6.34/2.26  tff(c_1260, plain, (![A_612]: (r1_tarski('#skF_6', u1_struct_0(A_612)) | ~m1_pre_topc('#skF_3', A_612) | ~l1_pre_topc(A_612))), inference(resolution, [status(thm)], [c_30, c_1245])).
% 6.34/2.26  tff(c_1070, plain, (![B_577, A_578]: (v2_pre_topc(B_577) | ~m1_pre_topc(B_577, A_578) | ~l1_pre_topc(A_578) | ~v2_pre_topc(A_578))), inference(cnfTransformation, [status(thm)], [f_50])).
% 6.34/2.26  tff(c_1079, plain, (v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_50, c_1070])).
% 6.34/2.26  tff(c_1088, plain, (v2_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_1079])).
% 6.34/2.26  tff(c_1507, plain, (![E_648, G_644, C_645, A_647, D_643, B_646]: (r1_tmap_1(D_643, A_647, k2_tmap_1(B_646, A_647, C_645, D_643), G_644) | ~r1_tmap_1(B_646, A_647, C_645, G_644) | ~r1_tarski(E_648, u1_struct_0(D_643)) | ~r2_hidden(G_644, E_648) | ~v3_pre_topc(E_648, B_646) | ~m1_subset_1(G_644, u1_struct_0(D_643)) | ~m1_subset_1(G_644, u1_struct_0(B_646)) | ~m1_subset_1(E_648, k1_zfmisc_1(u1_struct_0(B_646))) | ~m1_pre_topc(D_643, B_646) | v2_struct_0(D_643) | ~m1_subset_1(C_645, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_646), u1_struct_0(A_647)))) | ~v1_funct_2(C_645, u1_struct_0(B_646), u1_struct_0(A_647)) | ~v1_funct_1(C_645) | ~l1_pre_topc(B_646) | ~v2_pre_topc(B_646) | v2_struct_0(B_646) | ~l1_pre_topc(A_647) | ~v2_pre_topc(A_647) | v2_struct_0(A_647))), inference(cnfTransformation, [status(thm)], [f_189])).
% 6.34/2.26  tff(c_1525, plain, (![A_647, B_646, C_645, G_644]: (r1_tmap_1('#skF_3', A_647, k2_tmap_1(B_646, A_647, C_645, '#skF_3'), G_644) | ~r1_tmap_1(B_646, A_647, C_645, G_644) | ~r2_hidden(G_644, '#skF_6') | ~v3_pre_topc('#skF_6', B_646) | ~m1_subset_1(G_644, u1_struct_0('#skF_3')) | ~m1_subset_1(G_644, u1_struct_0(B_646)) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0(B_646))) | ~m1_pre_topc('#skF_3', B_646) | v2_struct_0('#skF_3') | ~m1_subset_1(C_645, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_646), u1_struct_0(A_647)))) | ~v1_funct_2(C_645, u1_struct_0(B_646), u1_struct_0(A_647)) | ~v1_funct_1(C_645) | ~l1_pre_topc(B_646) | ~v2_pre_topc(B_646) | v2_struct_0(B_646) | ~l1_pre_topc(A_647) | ~v2_pre_topc(A_647) | v2_struct_0(A_647))), inference(resolution, [status(thm)], [c_30, c_1507])).
% 6.34/2.26  tff(c_1796, plain, (![A_674, B_675, C_676, G_677]: (r1_tmap_1('#skF_3', A_674, k2_tmap_1(B_675, A_674, C_676, '#skF_3'), G_677) | ~r1_tmap_1(B_675, A_674, C_676, G_677) | ~r2_hidden(G_677, '#skF_6') | ~v3_pre_topc('#skF_6', B_675) | ~m1_subset_1(G_677, u1_struct_0('#skF_3')) | ~m1_subset_1(G_677, u1_struct_0(B_675)) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0(B_675))) | ~m1_pre_topc('#skF_3', B_675) | ~m1_subset_1(C_676, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_675), u1_struct_0(A_674)))) | ~v1_funct_2(C_676, u1_struct_0(B_675), u1_struct_0(A_674)) | ~v1_funct_1(C_676) | ~l1_pre_topc(B_675) | ~v2_pre_topc(B_675) | v2_struct_0(B_675) | ~l1_pre_topc(A_674) | ~v2_pre_topc(A_674) | v2_struct_0(A_674))), inference(negUnitSimplification, [status(thm)], [c_56, c_1525])).
% 6.34/2.26  tff(c_1798, plain, (![G_677]: (r1_tmap_1('#skF_3', '#skF_1', k2_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_3'), G_677) | ~r1_tmap_1('#skF_4', '#skF_1', '#skF_5', G_677) | ~r2_hidden(G_677, '#skF_6') | ~v3_pre_topc('#skF_6', '#skF_4') | ~m1_subset_1(G_677, u1_struct_0('#skF_3')) | ~m1_subset_1(G_677, u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_pre_topc('#skF_3', '#skF_4') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_44, c_1796])).
% 6.34/2.26  tff(c_1804, plain, (![G_677]: (r1_tmap_1('#skF_3', '#skF_1', k2_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_3'), G_677) | ~r1_tmap_1('#skF_4', '#skF_1', '#skF_5', G_677) | ~r2_hidden(G_677, '#skF_6') | ~v3_pre_topc('#skF_6', '#skF_4') | ~m1_subset_1(G_677, u1_struct_0('#skF_3')) | ~m1_subset_1(G_677, u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_struct_0('#skF_4') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_1088, c_102, c_48, c_46, c_42, c_1798])).
% 6.34/2.26  tff(c_1805, plain, (![G_677]: (r1_tmap_1('#skF_3', '#skF_1', k2_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_3'), G_677) | ~r1_tmap_1('#skF_4', '#skF_1', '#skF_5', G_677) | ~r2_hidden(G_677, '#skF_6') | ~v3_pre_topc('#skF_6', '#skF_4') | ~m1_subset_1(G_677, u1_struct_0('#skF_3')) | ~m1_subset_1(G_677, u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_68, c_52, c_1804])).
% 6.34/2.26  tff(c_1928, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(splitLeft, [status(thm)], [c_1805])).
% 6.34/2.26  tff(c_1932, plain, (~r1_tarski('#skF_6', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_6, c_1928])).
% 6.34/2.26  tff(c_1941, plain, (~m1_pre_topc('#skF_3', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_1260, c_1932])).
% 6.34/2.26  tff(c_1954, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_102, c_42, c_1941])).
% 6.34/2.26  tff(c_1956, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(splitRight, [status(thm)], [c_1805])).
% 6.34/2.26  tff(c_1966, plain, (r1_tarski('#skF_6', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_1956, c_4])).
% 6.34/2.26  tff(c_1280, plain, (![D_615, C_616, A_617]: (v3_pre_topc(D_615, C_616) | ~m1_subset_1(D_615, k1_zfmisc_1(u1_struct_0(C_616))) | ~v3_pre_topc(D_615, A_617) | ~m1_pre_topc(C_616, A_617) | ~m1_subset_1(D_615, k1_zfmisc_1(u1_struct_0(A_617))) | ~l1_pre_topc(A_617))), inference(cnfTransformation, [status(thm)], [f_74])).
% 6.34/2.26  tff(c_1776, plain, (![A_671, C_672, A_673]: (v3_pre_topc(A_671, C_672) | ~v3_pre_topc(A_671, A_673) | ~m1_pre_topc(C_672, A_673) | ~m1_subset_1(A_671, k1_zfmisc_1(u1_struct_0(A_673))) | ~l1_pre_topc(A_673) | ~r1_tarski(A_671, u1_struct_0(C_672)))), inference(resolution, [status(thm)], [c_6, c_1280])).
% 6.34/2.26  tff(c_1784, plain, (![A_671]: (v3_pre_topc(A_671, '#skF_4') | ~v3_pre_topc(A_671, '#skF_2') | ~m1_subset_1(A_671, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~r1_tarski(A_671, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_50, c_1776])).
% 6.34/2.26  tff(c_2712, plain, (![A_732]: (v3_pre_topc(A_732, '#skF_4') | ~v3_pre_topc(A_732, '#skF_2') | ~m1_subset_1(A_732, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~r1_tarski(A_732, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_1784])).
% 6.34/2.26  tff(c_2723, plain, (v3_pre_topc('#skF_6', '#skF_4') | ~v3_pre_topc('#skF_6', '#skF_2') | ~r1_tarski('#skF_6', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_40, c_2712])).
% 6.34/2.26  tff(c_2730, plain, (v3_pre_topc('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1966, c_34, c_2723])).
% 6.34/2.26  tff(c_1955, plain, (![G_677]: (~v3_pre_topc('#skF_6', '#skF_4') | r1_tmap_1('#skF_3', '#skF_1', k2_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_3'), G_677) | ~r1_tmap_1('#skF_4', '#skF_1', '#skF_5', G_677) | ~r2_hidden(G_677, '#skF_6') | ~m1_subset_1(G_677, u1_struct_0('#skF_3')) | ~m1_subset_1(G_677, u1_struct_0('#skF_4')))), inference(splitRight, [status(thm)], [c_1805])).
% 6.34/2.26  tff(c_3929, plain, (![G_810]: (r1_tmap_1('#skF_3', '#skF_1', k2_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_3'), G_810) | ~r1_tmap_1('#skF_4', '#skF_1', '#skF_5', G_810) | ~r2_hidden(G_810, '#skF_6') | ~m1_subset_1(G_810, u1_struct_0('#skF_3')) | ~m1_subset_1(G_810, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_2730, c_1955])).
% 6.34/2.26  tff(c_1428, plain, (![B_639, C_640, A_638, D_636, E_637]: (k3_tmap_1(A_638, B_639, C_640, D_636, E_637)=k2_partfun1(u1_struct_0(C_640), u1_struct_0(B_639), E_637, u1_struct_0(D_636)) | ~m1_pre_topc(D_636, C_640) | ~m1_subset_1(E_637, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_640), u1_struct_0(B_639)))) | ~v1_funct_2(E_637, u1_struct_0(C_640), u1_struct_0(B_639)) | ~v1_funct_1(E_637) | ~m1_pre_topc(D_636, A_638) | ~m1_pre_topc(C_640, A_638) | ~l1_pre_topc(B_639) | ~v2_pre_topc(B_639) | v2_struct_0(B_639) | ~l1_pre_topc(A_638) | ~v2_pre_topc(A_638) | v2_struct_0(A_638))), inference(cnfTransformation, [status(thm)], [f_133])).
% 6.34/2.26  tff(c_1430, plain, (![A_638, D_636]: (k3_tmap_1(A_638, '#skF_1', '#skF_4', D_636, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0(D_636)) | ~m1_pre_topc(D_636, '#skF_4') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_636, A_638) | ~m1_pre_topc('#skF_4', A_638) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~l1_pre_topc(A_638) | ~v2_pre_topc(A_638) | v2_struct_0(A_638))), inference(resolution, [status(thm)], [c_44, c_1428])).
% 6.34/2.26  tff(c_1436, plain, (![A_638, D_636]: (k3_tmap_1(A_638, '#skF_1', '#skF_4', D_636, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0(D_636)) | ~m1_pre_topc(D_636, '#skF_4') | ~m1_pre_topc(D_636, A_638) | ~m1_pre_topc('#skF_4', A_638) | v2_struct_0('#skF_1') | ~l1_pre_topc(A_638) | ~v2_pre_topc(A_638) | v2_struct_0(A_638))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_48, c_46, c_1430])).
% 6.34/2.26  tff(c_1446, plain, (![A_641, D_642]: (k3_tmap_1(A_641, '#skF_1', '#skF_4', D_642, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0(D_642)) | ~m1_pre_topc(D_642, '#skF_4') | ~m1_pre_topc(D_642, A_641) | ~m1_pre_topc('#skF_4', A_641) | ~l1_pre_topc(A_641) | ~v2_pre_topc(A_641) | v2_struct_0(A_641))), inference(negUnitSimplification, [status(thm)], [c_68, c_1436])).
% 6.34/2.26  tff(c_1450, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5') | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_54, c_1446])).
% 6.34/2.26  tff(c_1460, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_50, c_42, c_1450])).
% 6.34/2.26  tff(c_1461, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_62, c_1460])).
% 6.34/2.26  tff(c_1385, plain, (![A_627, B_628, C_629, D_630]: (k2_partfun1(u1_struct_0(A_627), u1_struct_0(B_628), C_629, u1_struct_0(D_630))=k2_tmap_1(A_627, B_628, C_629, D_630) | ~m1_pre_topc(D_630, A_627) | ~m1_subset_1(C_629, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_627), u1_struct_0(B_628)))) | ~v1_funct_2(C_629, u1_struct_0(A_627), u1_struct_0(B_628)) | ~v1_funct_1(C_629) | ~l1_pre_topc(B_628) | ~v2_pre_topc(B_628) | v2_struct_0(B_628) | ~l1_pre_topc(A_627) | ~v2_pre_topc(A_627) | v2_struct_0(A_627))), inference(cnfTransformation, [status(thm)], [f_101])).
% 6.34/2.26  tff(c_1387, plain, (![D_630]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0(D_630))=k2_tmap_1('#skF_4', '#skF_1', '#skF_5', D_630) | ~m1_pre_topc(D_630, '#skF_4') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_44, c_1385])).
% 6.34/2.26  tff(c_1393, plain, (![D_630]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0(D_630))=k2_tmap_1('#skF_4', '#skF_1', '#skF_5', D_630) | ~m1_pre_topc(D_630, '#skF_4') | v2_struct_0('#skF_1') | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1088, c_102, c_66, c_64, c_48, c_46, c_1387])).
% 6.34/2.26  tff(c_1394, plain, (![D_630]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0(D_630))=k2_tmap_1('#skF_4', '#skF_1', '#skF_5', D_630) | ~m1_pre_topc(D_630, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_52, c_68, c_1393])).
% 6.34/2.26  tff(c_1473, plain, (k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5')=k2_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1461, c_1394])).
% 6.34/2.26  tff(c_1480, plain, (k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5')=k2_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_1473])).
% 6.34/2.26  tff(c_1024, plain, (~r1_tmap_1('#skF_3', '#skF_1', k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5'), '#skF_8')), inference(splitRight, [status(thm)], [c_78])).
% 6.34/2.26  tff(c_1026, plain, (r1_tmap_1('#skF_3', '#skF_1', k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5'), '#skF_8')), inference(splitLeft, [status(thm)], [c_77])).
% 6.34/2.26  tff(c_1066, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1024, c_1026])).
% 6.34/2.26  tff(c_1068, plain, (~r1_tmap_1('#skF_3', '#skF_1', k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5'), '#skF_8')), inference(splitRight, [status(thm)], [c_77])).
% 6.34/2.26  tff(c_1485, plain, (~r1_tmap_1('#skF_3', '#skF_1', k2_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_3'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_1480, c_1068])).
% 6.34/2.26  tff(c_3934, plain, (~r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_8') | ~r2_hidden('#skF_8', '#skF_6') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_3929, c_1485])).
% 6.34/2.26  tff(c_3942, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_79, c_36, c_80, c_1025, c_3934])).
% 6.34/2.26  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.34/2.26  
% 6.34/2.26  Inference rules
% 6.34/2.26  ----------------------
% 6.34/2.26  #Ref     : 0
% 6.34/2.26  #Sup     : 841
% 6.34/2.26  #Fact    : 0
% 6.34/2.26  #Define  : 0
% 6.34/2.26  #Split   : 28
% 6.34/2.26  #Chain   : 0
% 6.34/2.26  #Close   : 0
% 6.34/2.26  
% 6.34/2.26  Ordering : KBO
% 6.34/2.26  
% 6.34/2.26  Simplification rules
% 6.34/2.26  ----------------------
% 6.34/2.26  #Subsume      : 408
% 6.34/2.26  #Demod        : 658
% 6.34/2.26  #Tautology    : 135
% 6.34/2.26  #SimpNegUnit  : 45
% 6.34/2.26  #BackRed      : 4
% 6.34/2.26  
% 6.34/2.26  #Partial instantiations: 0
% 6.34/2.26  #Strategies tried      : 1
% 6.34/2.26  
% 6.34/2.26  Timing (in seconds)
% 6.34/2.26  ----------------------
% 6.34/2.26  Preprocessing        : 0.42
% 6.34/2.26  Parsing              : 0.21
% 6.34/2.26  CNF conversion       : 0.07
% 6.34/2.26  Main loop            : 1.04
% 6.34/2.26  Inferencing          : 0.34
% 6.34/2.26  Reduction            : 0.33
% 6.34/2.26  Demodulation         : 0.23
% 6.34/2.26  BG Simplification    : 0.03
% 6.34/2.26  Subsumption          : 0.26
% 6.34/2.26  Abstraction          : 0.04
% 6.34/2.26  MUC search           : 0.00
% 6.34/2.26  Cooper               : 0.00
% 6.34/2.26  Total                : 1.52
% 6.34/2.26  Index Insertion      : 0.00
% 6.34/2.26  Index Deletion       : 0.00
% 6.34/2.26  Index Matching       : 0.00
% 6.34/2.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
