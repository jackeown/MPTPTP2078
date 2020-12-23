%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:46 EST 2020

% Result     : Theorem 5.22s
% Output     : CNFRefutation 5.31s
% Verified   : 
% Statistics : Number of formulae       :  191 (14266 expanded)
%              Number of leaves         :   42 (5621 expanded)
%              Depth                    :   37
%              Number of atoms          :  853 (97745 expanded)
%              Number of equality atoms :   57 (6955 expanded)
%              Maximal formula depth    :   22 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_funct_2 > v1_funct_2 > r2_hidden > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k3_funct_2 > k2_tmap_1 > k2_partfun1 > k4_tmap_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_344,negated_conjecture,(
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

tff(f_197,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_pre_topc(B,A) )
     => ( v1_funct_1(k4_tmap_1(A,B))
        & v1_funct_2(k4_tmap_1(A,B),u1_struct_0(B),u1_struct_0(A))
        & m1_subset_1(k4_tmap_1(A,B),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B),u1_struct_0(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_tmap_1)).

tff(f_61,axiom,(
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

tff(f_70,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_77,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_208,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_182,axiom,(
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

tff(f_282,axiom,(
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

tff(f_152,axiom,(
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

tff(f_120,axiom,(
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

tff(f_252,axiom,(
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

tff(f_93,axiom,(
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

tff(f_314,axiom,(
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

tff(f_45,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => k3_funct_2(A,B,C,D) = k1_funct_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

tff(f_204,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_32,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(c_66,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_344])).

tff(c_64,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_344])).

tff(c_62,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_344])).

tff(c_58,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_344])).

tff(c_26,plain,(
    ! [A_76,B_77] :
      ( m1_subset_1(k4_tmap_1(A_76,B_77),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_77),u1_struct_0(A_76))))
      | ~ m1_pre_topc(B_77,A_76)
      | ~ l1_pre_topc(A_76)
      | ~ v2_pre_topc(A_76)
      | v2_struct_0(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_60,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_344])).

tff(c_56,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_344])).

tff(c_54,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_344])).

tff(c_52,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_344])).

tff(c_117,plain,(
    ! [A_205,B_206,D_207] :
      ( r2_funct_2(A_205,B_206,D_207,D_207)
      | ~ m1_subset_1(D_207,k1_zfmisc_1(k2_zfmisc_1(A_205,B_206)))
      | ~ v1_funct_2(D_207,A_205,B_206)
      | ~ v1_funct_1(D_207) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_119,plain,
    ( r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4','#skF_4')
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_117])).

tff(c_122,plain,(
    r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_119])).

tff(c_30,plain,(
    ! [A_76,B_77] :
      ( v1_funct_1(k4_tmap_1(A_76,B_77))
      | ~ m1_pre_topc(B_77,A_76)
      | ~ l1_pre_topc(A_76)
      | ~ v2_pre_topc(A_76)
      | v2_struct_0(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_83,plain,(
    ! [B_191,A_192] :
      ( v2_pre_topc(B_191)
      | ~ m1_pre_topc(B_191,A_192)
      | ~ l1_pre_topc(A_192)
      | ~ v2_pre_topc(A_192) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_89,plain,
    ( v2_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_58,c_83])).

tff(c_93,plain,(
    v2_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_89])).

tff(c_68,plain,(
    ! [B_186,A_187] :
      ( l1_pre_topc(B_186)
      | ~ m1_pre_topc(B_186,A_187)
      | ~ l1_pre_topc(A_187) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_74,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_58,c_68])).

tff(c_78,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_74])).

tff(c_34,plain,(
    ! [A_81] :
      ( m1_pre_topc(A_81,A_81)
      | ~ l1_pre_topc(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_157,plain,(
    ! [B_237,D_238,E_235,C_239,A_236] :
      ( v1_funct_1(k3_tmap_1(A_236,B_237,C_239,D_238,E_235))
      | ~ m1_subset_1(E_235,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_239),u1_struct_0(B_237))))
      | ~ v1_funct_2(E_235,u1_struct_0(C_239),u1_struct_0(B_237))
      | ~ v1_funct_1(E_235)
      | ~ m1_pre_topc(D_238,A_236)
      | ~ m1_pre_topc(C_239,A_236)
      | ~ l1_pre_topc(B_237)
      | ~ v2_pre_topc(B_237)
      | v2_struct_0(B_237)
      | ~ l1_pre_topc(A_236)
      | ~ v2_pre_topc(A_236)
      | v2_struct_0(A_236) ) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_161,plain,(
    ! [A_236,D_238] :
      ( v1_funct_1(k3_tmap_1(A_236,'#skF_2','#skF_3',D_238,'#skF_4'))
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_4')
      | ~ m1_pre_topc(D_238,A_236)
      | ~ m1_pre_topc('#skF_3',A_236)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_236)
      | ~ v2_pre_topc(A_236)
      | v2_struct_0(A_236) ) ),
    inference(resolution,[status(thm)],[c_52,c_157])).

tff(c_165,plain,(
    ! [A_236,D_238] :
      ( v1_funct_1(k3_tmap_1(A_236,'#skF_2','#skF_3',D_238,'#skF_4'))
      | ~ m1_pre_topc(D_238,A_236)
      | ~ m1_pre_topc('#skF_3',A_236)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_236)
      | ~ v2_pre_topc(A_236)
      | v2_struct_0(A_236) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_56,c_54,c_161])).

tff(c_166,plain,(
    ! [A_236,D_238] :
      ( v1_funct_1(k3_tmap_1(A_236,'#skF_2','#skF_3',D_238,'#skF_4'))
      | ~ m1_pre_topc(D_238,A_236)
      | ~ m1_pre_topc('#skF_3',A_236)
      | ~ l1_pre_topc(A_236)
      | ~ v2_pre_topc(A_236)
      | v2_struct_0(A_236) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_165])).

tff(c_193,plain,(
    ! [E_255,C_259,A_256,D_258,B_257] :
      ( v1_funct_2(k3_tmap_1(A_256,B_257,C_259,D_258,E_255),u1_struct_0(D_258),u1_struct_0(B_257))
      | ~ m1_subset_1(E_255,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_259),u1_struct_0(B_257))))
      | ~ v1_funct_2(E_255,u1_struct_0(C_259),u1_struct_0(B_257))
      | ~ v1_funct_1(E_255)
      | ~ m1_pre_topc(D_258,A_256)
      | ~ m1_pre_topc(C_259,A_256)
      | ~ l1_pre_topc(B_257)
      | ~ v2_pre_topc(B_257)
      | v2_struct_0(B_257)
      | ~ l1_pre_topc(A_256)
      | ~ v2_pre_topc(A_256)
      | v2_struct_0(A_256) ) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_197,plain,(
    ! [A_256,D_258] :
      ( v1_funct_2(k3_tmap_1(A_256,'#skF_2','#skF_3',D_258,'#skF_4'),u1_struct_0(D_258),u1_struct_0('#skF_2'))
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_4')
      | ~ m1_pre_topc(D_258,A_256)
      | ~ m1_pre_topc('#skF_3',A_256)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_256)
      | ~ v2_pre_topc(A_256)
      | v2_struct_0(A_256) ) ),
    inference(resolution,[status(thm)],[c_52,c_193])).

tff(c_201,plain,(
    ! [A_256,D_258] :
      ( v1_funct_2(k3_tmap_1(A_256,'#skF_2','#skF_3',D_258,'#skF_4'),u1_struct_0(D_258),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_258,A_256)
      | ~ m1_pre_topc('#skF_3',A_256)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_256)
      | ~ v2_pre_topc(A_256)
      | v2_struct_0(A_256) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_56,c_54,c_197])).

tff(c_202,plain,(
    ! [A_256,D_258] :
      ( v1_funct_2(k3_tmap_1(A_256,'#skF_2','#skF_3',D_258,'#skF_4'),u1_struct_0(D_258),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_258,A_256)
      | ~ m1_pre_topc('#skF_3',A_256)
      | ~ l1_pre_topc(A_256)
      | ~ v2_pre_topc(A_256)
      | v2_struct_0(A_256) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_201])).

tff(c_20,plain,(
    ! [D_74,C_73,B_72,E_75,A_71] :
      ( m1_subset_1(k3_tmap_1(A_71,B_72,C_73,D_74,E_75),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_74),u1_struct_0(B_72))))
      | ~ m1_subset_1(E_75,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_73),u1_struct_0(B_72))))
      | ~ v1_funct_2(E_75,u1_struct_0(C_73),u1_struct_0(B_72))
      | ~ v1_funct_1(E_75)
      | ~ m1_pre_topc(D_74,A_71)
      | ~ m1_pre_topc(C_73,A_71)
      | ~ l1_pre_topc(B_72)
      | ~ v2_pre_topc(B_72)
      | v2_struct_0(B_72)
      | ~ l1_pre_topc(A_71)
      | ~ v2_pre_topc(A_71)
      | v2_struct_0(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_204,plain,(
    ! [C_262,B_263,D_264,A_265] :
      ( r2_funct_2(u1_struct_0(C_262),u1_struct_0(B_263),D_264,k3_tmap_1(A_265,B_263,C_262,C_262,D_264))
      | ~ m1_subset_1(D_264,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_262),u1_struct_0(B_263))))
      | ~ v1_funct_2(D_264,u1_struct_0(C_262),u1_struct_0(B_263))
      | ~ v1_funct_1(D_264)
      | ~ m1_pre_topc(C_262,A_265)
      | v2_struct_0(C_262)
      | ~ l1_pre_topc(B_263)
      | ~ v2_pre_topc(B_263)
      | v2_struct_0(B_263)
      | ~ l1_pre_topc(A_265)
      | ~ v2_pre_topc(A_265)
      | v2_struct_0(A_265) ) ),
    inference(cnfTransformation,[status(thm)],[f_282])).

tff(c_208,plain,(
    ! [A_265] :
      ( r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',k3_tmap_1(A_265,'#skF_2','#skF_3','#skF_3','#skF_4'))
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_4')
      | ~ m1_pre_topc('#skF_3',A_265)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_265)
      | ~ v2_pre_topc(A_265)
      | v2_struct_0(A_265) ) ),
    inference(resolution,[status(thm)],[c_52,c_204])).

tff(c_212,plain,(
    ! [A_265] :
      ( r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',k3_tmap_1(A_265,'#skF_2','#skF_3','#skF_3','#skF_4'))
      | ~ m1_pre_topc('#skF_3',A_265)
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_265)
      | ~ v2_pre_topc(A_265)
      | v2_struct_0(A_265) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_56,c_54,c_208])).

tff(c_236,plain,(
    ! [A_271] :
      ( r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',k3_tmap_1(A_271,'#skF_2','#skF_3','#skF_3','#skF_4'))
      | ~ m1_pre_topc('#skF_3',A_271)
      | ~ l1_pre_topc(A_271)
      | ~ v2_pre_topc(A_271)
      | v2_struct_0(A_271) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_60,c_212])).

tff(c_8,plain,(
    ! [D_11,C_10,A_8,B_9] :
      ( D_11 = C_10
      | ~ r2_funct_2(A_8,B_9,C_10,D_11)
      | ~ m1_subset_1(D_11,k1_zfmisc_1(k2_zfmisc_1(A_8,B_9)))
      | ~ v1_funct_2(D_11,A_8,B_9)
      | ~ v1_funct_1(D_11)
      | ~ m1_subset_1(C_10,k1_zfmisc_1(k2_zfmisc_1(A_8,B_9)))
      | ~ v1_funct_2(C_10,A_8,B_9)
      | ~ v1_funct_1(C_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_238,plain,(
    ! [A_271] :
      ( k3_tmap_1(A_271,'#skF_2','#skF_3','#skF_3','#skF_4') = '#skF_4'
      | ~ m1_subset_1(k3_tmap_1(A_271,'#skF_2','#skF_3','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(k3_tmap_1(A_271,'#skF_2','#skF_3','#skF_3','#skF_4'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k3_tmap_1(A_271,'#skF_2','#skF_3','#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_4')
      | ~ m1_pre_topc('#skF_3',A_271)
      | ~ l1_pre_topc(A_271)
      | ~ v2_pre_topc(A_271)
      | v2_struct_0(A_271) ) ),
    inference(resolution,[status(thm)],[c_236,c_8])).

tff(c_252,plain,(
    ! [A_279] :
      ( k3_tmap_1(A_279,'#skF_2','#skF_3','#skF_3','#skF_4') = '#skF_4'
      | ~ m1_subset_1(k3_tmap_1(A_279,'#skF_2','#skF_3','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(k3_tmap_1(A_279,'#skF_2','#skF_3','#skF_3','#skF_4'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k3_tmap_1(A_279,'#skF_2','#skF_3','#skF_3','#skF_4'))
      | ~ m1_pre_topc('#skF_3',A_279)
      | ~ l1_pre_topc(A_279)
      | ~ v2_pre_topc(A_279)
      | v2_struct_0(A_279) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_238])).

tff(c_256,plain,(
    ! [A_71] :
      ( k3_tmap_1(A_71,'#skF_2','#skF_3','#skF_3','#skF_4') = '#skF_4'
      | ~ v1_funct_2(k3_tmap_1(A_71,'#skF_2','#skF_3','#skF_3','#skF_4'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k3_tmap_1(A_71,'#skF_2','#skF_3','#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_4')
      | ~ m1_pre_topc('#skF_3',A_71)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_71)
      | ~ v2_pre_topc(A_71)
      | v2_struct_0(A_71) ) ),
    inference(resolution,[status(thm)],[c_20,c_252])).

tff(c_259,plain,(
    ! [A_71] :
      ( k3_tmap_1(A_71,'#skF_2','#skF_3','#skF_3','#skF_4') = '#skF_4'
      | ~ v1_funct_2(k3_tmap_1(A_71,'#skF_2','#skF_3','#skF_3','#skF_4'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k3_tmap_1(A_71,'#skF_2','#skF_3','#skF_3','#skF_4'))
      | ~ m1_pre_topc('#skF_3',A_71)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_71)
      | ~ v2_pre_topc(A_71)
      | v2_struct_0(A_71) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_56,c_54,c_52,c_256])).

tff(c_261,plain,(
    ! [A_280] :
      ( k3_tmap_1(A_280,'#skF_2','#skF_3','#skF_3','#skF_4') = '#skF_4'
      | ~ v1_funct_2(k3_tmap_1(A_280,'#skF_2','#skF_3','#skF_3','#skF_4'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k3_tmap_1(A_280,'#skF_2','#skF_3','#skF_3','#skF_4'))
      | ~ m1_pre_topc('#skF_3',A_280)
      | ~ l1_pre_topc(A_280)
      | ~ v2_pre_topc(A_280)
      | v2_struct_0(A_280) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_259])).

tff(c_267,plain,(
    ! [A_281] :
      ( k3_tmap_1(A_281,'#skF_2','#skF_3','#skF_3','#skF_4') = '#skF_4'
      | ~ v1_funct_1(k3_tmap_1(A_281,'#skF_2','#skF_3','#skF_3','#skF_4'))
      | ~ m1_pre_topc('#skF_3',A_281)
      | ~ l1_pre_topc(A_281)
      | ~ v2_pre_topc(A_281)
      | v2_struct_0(A_281) ) ),
    inference(resolution,[status(thm)],[c_202,c_261])).

tff(c_273,plain,(
    ! [A_282] :
      ( k3_tmap_1(A_282,'#skF_2','#skF_3','#skF_3','#skF_4') = '#skF_4'
      | ~ m1_pre_topc('#skF_3',A_282)
      | ~ l1_pre_topc(A_282)
      | ~ v2_pre_topc(A_282)
      | v2_struct_0(A_282) ) ),
    inference(resolution,[status(thm)],[c_166,c_267])).

tff(c_280,plain,
    ( k3_tmap_1('#skF_2','#skF_2','#skF_3','#skF_3','#skF_4') = '#skF_4'
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_58,c_273])).

tff(c_287,plain,
    ( k3_tmap_1('#skF_2','#skF_2','#skF_3','#skF_3','#skF_4') = '#skF_4'
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_280])).

tff(c_288,plain,(
    k3_tmap_1('#skF_2','#skF_2','#skF_3','#skF_3','#skF_4') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_287])).

tff(c_345,plain,(
    ! [C_285,E_287,A_284,B_283,D_286] :
      ( k3_tmap_1(A_284,B_283,C_285,D_286,E_287) = k2_partfun1(u1_struct_0(C_285),u1_struct_0(B_283),E_287,u1_struct_0(D_286))
      | ~ m1_pre_topc(D_286,C_285)
      | ~ m1_subset_1(E_287,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_285),u1_struct_0(B_283))))
      | ~ v1_funct_2(E_287,u1_struct_0(C_285),u1_struct_0(B_283))
      | ~ v1_funct_1(E_287)
      | ~ m1_pre_topc(D_286,A_284)
      | ~ m1_pre_topc(C_285,A_284)
      | ~ l1_pre_topc(B_283)
      | ~ v2_pre_topc(B_283)
      | v2_struct_0(B_283)
      | ~ l1_pre_topc(A_284)
      | ~ v2_pre_topc(A_284)
      | v2_struct_0(A_284) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_351,plain,(
    ! [A_284,D_286] :
      ( k3_tmap_1(A_284,'#skF_2','#skF_3',D_286,'#skF_4') = k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',u1_struct_0(D_286))
      | ~ m1_pre_topc(D_286,'#skF_3')
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_4')
      | ~ m1_pre_topc(D_286,A_284)
      | ~ m1_pre_topc('#skF_3',A_284)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_284)
      | ~ v2_pre_topc(A_284)
      | v2_struct_0(A_284) ) ),
    inference(resolution,[status(thm)],[c_52,c_345])).

tff(c_356,plain,(
    ! [A_284,D_286] :
      ( k3_tmap_1(A_284,'#skF_2','#skF_3',D_286,'#skF_4') = k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',u1_struct_0(D_286))
      | ~ m1_pre_topc(D_286,'#skF_3')
      | ~ m1_pre_topc(D_286,A_284)
      | ~ m1_pre_topc('#skF_3',A_284)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_284)
      | ~ v2_pre_topc(A_284)
      | v2_struct_0(A_284) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_56,c_54,c_351])).

tff(c_358,plain,(
    ! [A_288,D_289] :
      ( k3_tmap_1(A_288,'#skF_2','#skF_3',D_289,'#skF_4') = k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',u1_struct_0(D_289))
      | ~ m1_pre_topc(D_289,'#skF_3')
      | ~ m1_pre_topc(D_289,A_288)
      | ~ m1_pre_topc('#skF_3',A_288)
      | ~ l1_pre_topc(A_288)
      | ~ v2_pre_topc(A_288)
      | v2_struct_0(A_288) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_356])).

tff(c_362,plain,
    ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_2','#skF_2','#skF_3','#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_58,c_358])).

tff(c_366,plain,
    ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',u1_struct_0('#skF_3')) = '#skF_4'
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_58,c_288,c_362])).

tff(c_367,plain,
    ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',u1_struct_0('#skF_3')) = '#skF_4'
    | ~ m1_pre_topc('#skF_3','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_366])).

tff(c_368,plain,(
    ~ m1_pre_topc('#skF_3','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_367])).

tff(c_371,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_368])).

tff(c_375,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_371])).

tff(c_377,plain,(
    m1_pre_topc('#skF_3','#skF_3') ),
    inference(splitRight,[status(thm)],[c_367])).

tff(c_376,plain,(
    k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',u1_struct_0('#skF_3')) = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_367])).

tff(c_167,plain,(
    ! [A_240,B_241,C_242,D_243] :
      ( k2_partfun1(u1_struct_0(A_240),u1_struct_0(B_241),C_242,u1_struct_0(D_243)) = k2_tmap_1(A_240,B_241,C_242,D_243)
      | ~ m1_pre_topc(D_243,A_240)
      | ~ m1_subset_1(C_242,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_240),u1_struct_0(B_241))))
      | ~ v1_funct_2(C_242,u1_struct_0(A_240),u1_struct_0(B_241))
      | ~ v1_funct_1(C_242)
      | ~ l1_pre_topc(B_241)
      | ~ v2_pre_topc(B_241)
      | v2_struct_0(B_241)
      | ~ l1_pre_topc(A_240)
      | ~ v2_pre_topc(A_240)
      | v2_struct_0(A_240) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_171,plain,(
    ! [D_243] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',u1_struct_0(D_243)) = k2_tmap_1('#skF_3','#skF_2','#skF_4',D_243)
      | ~ m1_pre_topc(D_243,'#skF_3')
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_52,c_167])).

tff(c_175,plain,(
    ! [D_243] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',u1_struct_0(D_243)) = k2_tmap_1('#skF_3','#skF_2','#skF_4',D_243)
      | ~ m1_pre_topc(D_243,'#skF_3')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_78,c_64,c_62,c_56,c_54,c_171])).

tff(c_176,plain,(
    ! [D_243] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',u1_struct_0(D_243)) = k2_tmap_1('#skF_3','#skF_2','#skF_4',D_243)
      | ~ m1_pre_topc(D_243,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_66,c_175])).

tff(c_409,plain,
    ( k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_3') = '#skF_4'
    | ~ m1_pre_topc('#skF_3','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_376,c_176])).

tff(c_416,plain,(
    k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_377,c_409])).

tff(c_473,plain,(
    ! [C_293,B_291,A_295,E_294,D_292] :
      ( r2_hidden('#skF_1'(B_291,D_292,C_293,E_294,A_295),u1_struct_0(C_293))
      | r2_funct_2(u1_struct_0(C_293),u1_struct_0(A_295),k2_tmap_1(B_291,A_295,D_292,C_293),E_294)
      | ~ m1_subset_1(E_294,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_293),u1_struct_0(A_295))))
      | ~ v1_funct_2(E_294,u1_struct_0(C_293),u1_struct_0(A_295))
      | ~ v1_funct_1(E_294)
      | ~ m1_subset_1(D_292,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_291),u1_struct_0(A_295))))
      | ~ v1_funct_2(D_292,u1_struct_0(B_291),u1_struct_0(A_295))
      | ~ v1_funct_1(D_292)
      | ~ m1_pre_topc(C_293,B_291)
      | v2_struct_0(C_293)
      | ~ l1_pre_topc(B_291)
      | ~ v2_pre_topc(B_291)
      | v2_struct_0(B_291)
      | ~ l1_pre_topc(A_295)
      | ~ v2_pre_topc(A_295)
      | v2_struct_0(A_295) ) ),
    inference(cnfTransformation,[status(thm)],[f_252])).

tff(c_1162,plain,(
    ! [B_373,D_374,B_375,A_376] :
      ( r2_hidden('#skF_1'(B_373,D_374,B_375,k4_tmap_1(A_376,B_375),A_376),u1_struct_0(B_375))
      | r2_funct_2(u1_struct_0(B_375),u1_struct_0(A_376),k2_tmap_1(B_373,A_376,D_374,B_375),k4_tmap_1(A_376,B_375))
      | ~ v1_funct_2(k4_tmap_1(A_376,B_375),u1_struct_0(B_375),u1_struct_0(A_376))
      | ~ v1_funct_1(k4_tmap_1(A_376,B_375))
      | ~ m1_subset_1(D_374,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_373),u1_struct_0(A_376))))
      | ~ v1_funct_2(D_374,u1_struct_0(B_373),u1_struct_0(A_376))
      | ~ v1_funct_1(D_374)
      | ~ m1_pre_topc(B_375,B_373)
      | v2_struct_0(B_375)
      | ~ l1_pre_topc(B_373)
      | ~ v2_pre_topc(B_373)
      | v2_struct_0(B_373)
      | ~ m1_pre_topc(B_375,A_376)
      | ~ l1_pre_topc(A_376)
      | ~ v2_pre_topc(A_376)
      | v2_struct_0(A_376) ) ),
    inference(resolution,[status(thm)],[c_26,c_473])).

tff(c_1167,plain,
    ( r2_hidden('#skF_1'('#skF_3','#skF_4','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_2'),u1_struct_0('#skF_3'))
    | r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',k4_tmap_1('#skF_2','#skF_3'))
    | ~ v1_funct_2(k4_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k4_tmap_1('#skF_2','#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_416,c_1162])).

tff(c_1170,plain,
    ( r2_hidden('#skF_1'('#skF_3','#skF_4','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_2'),u1_struct_0('#skF_3'))
    | r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',k4_tmap_1('#skF_2','#skF_3'))
    | ~ v1_funct_2(k4_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k4_tmap_1('#skF_2','#skF_3'))
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_58,c_93,c_78,c_377,c_56,c_54,c_52,c_1167])).

tff(c_1171,plain,
    ( r2_hidden('#skF_1'('#skF_3','#skF_4','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_2'),u1_struct_0('#skF_3'))
    | r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',k4_tmap_1('#skF_2','#skF_3'))
    | ~ v1_funct_2(k4_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k4_tmap_1('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_60,c_1170])).

tff(c_1172,plain,(
    ~ v1_funct_1(k4_tmap_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1171])).

tff(c_1175,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_1172])).

tff(c_1178,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_58,c_1175])).

tff(c_1180,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_1178])).

tff(c_1182,plain,(
    v1_funct_1(k4_tmap_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1171])).

tff(c_28,plain,(
    ! [A_76,B_77] :
      ( v1_funct_2(k4_tmap_1(A_76,B_77),u1_struct_0(B_77),u1_struct_0(A_76))
      | ~ m1_pre_topc(B_77,A_76)
      | ~ l1_pre_topc(A_76)
      | ~ v2_pre_topc(A_76)
      | v2_struct_0(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_1181,plain,
    ( ~ v1_funct_2(k4_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',k4_tmap_1('#skF_2','#skF_3'))
    | r2_hidden('#skF_1'('#skF_3','#skF_4','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_2'),u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1171])).

tff(c_1190,plain,(
    ~ v1_funct_2(k4_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_1181])).

tff(c_1193,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_1190])).

tff(c_1196,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_58,c_1193])).

tff(c_1198,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_1196])).

tff(c_1200,plain,(
    v1_funct_2(k4_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_1181])).

tff(c_1199,plain,
    ( r2_hidden('#skF_1'('#skF_3','#skF_4','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_2'),u1_struct_0('#skF_3'))
    | r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',k4_tmap_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1181])).

tff(c_1201,plain,(
    r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',k4_tmap_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1199])).

tff(c_1203,plain,
    ( k4_tmap_1('#skF_2','#skF_3') = '#skF_4'
    | ~ m1_subset_1(k4_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k4_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k4_tmap_1('#skF_2','#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1201,c_8])).

tff(c_1206,plain,
    ( k4_tmap_1('#skF_2','#skF_3') = '#skF_4'
    | ~ m1_subset_1(k4_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_1182,c_1200,c_1203])).

tff(c_1223,plain,(
    ~ m1_subset_1(k4_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_1206])).

tff(c_1226,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_1223])).

tff(c_1229,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_58,c_1226])).

tff(c_1231,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_1229])).

tff(c_1232,plain,(
    k4_tmap_1('#skF_2','#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1206])).

tff(c_48,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k4_tmap_1('#skF_2','#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_344])).

tff(c_1237,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1232,c_48])).

tff(c_1243,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_1237])).

tff(c_1245,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',k4_tmap_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1199])).

tff(c_676,plain,(
    ! [B_307,D_308,A_311,E_310,C_309] :
      ( m1_subset_1('#skF_1'(B_307,D_308,C_309,E_310,A_311),u1_struct_0(B_307))
      | r2_funct_2(u1_struct_0(C_309),u1_struct_0(A_311),k2_tmap_1(B_307,A_311,D_308,C_309),E_310)
      | ~ m1_subset_1(E_310,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_309),u1_struct_0(A_311))))
      | ~ v1_funct_2(E_310,u1_struct_0(C_309),u1_struct_0(A_311))
      | ~ v1_funct_1(E_310)
      | ~ m1_subset_1(D_308,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_307),u1_struct_0(A_311))))
      | ~ v1_funct_2(D_308,u1_struct_0(B_307),u1_struct_0(A_311))
      | ~ v1_funct_1(D_308)
      | ~ m1_pre_topc(C_309,B_307)
      | v2_struct_0(C_309)
      | ~ l1_pre_topc(B_307)
      | ~ v2_pre_topc(B_307)
      | v2_struct_0(B_307)
      | ~ l1_pre_topc(A_311)
      | ~ v2_pre_topc(A_311)
      | v2_struct_0(A_311) ) ),
    inference(cnfTransformation,[status(thm)],[f_252])).

tff(c_1275,plain,(
    ! [B_387,D_388,B_389,A_390] :
      ( m1_subset_1('#skF_1'(B_387,D_388,B_389,k4_tmap_1(A_390,B_389),A_390),u1_struct_0(B_387))
      | r2_funct_2(u1_struct_0(B_389),u1_struct_0(A_390),k2_tmap_1(B_387,A_390,D_388,B_389),k4_tmap_1(A_390,B_389))
      | ~ v1_funct_2(k4_tmap_1(A_390,B_389),u1_struct_0(B_389),u1_struct_0(A_390))
      | ~ v1_funct_1(k4_tmap_1(A_390,B_389))
      | ~ m1_subset_1(D_388,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_387),u1_struct_0(A_390))))
      | ~ v1_funct_2(D_388,u1_struct_0(B_387),u1_struct_0(A_390))
      | ~ v1_funct_1(D_388)
      | ~ m1_pre_topc(B_389,B_387)
      | v2_struct_0(B_389)
      | ~ l1_pre_topc(B_387)
      | ~ v2_pre_topc(B_387)
      | v2_struct_0(B_387)
      | ~ m1_pre_topc(B_389,A_390)
      | ~ l1_pre_topc(A_390)
      | ~ v2_pre_topc(A_390)
      | v2_struct_0(A_390) ) ),
    inference(resolution,[status(thm)],[c_26,c_676])).

tff(c_1286,plain,
    ( m1_subset_1('#skF_1'('#skF_3','#skF_4','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_2'),u1_struct_0('#skF_3'))
    | r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',k4_tmap_1('#skF_2','#skF_3'))
    | ~ v1_funct_2(k4_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k4_tmap_1('#skF_2','#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_416,c_1275])).

tff(c_1291,plain,
    ( m1_subset_1('#skF_1'('#skF_3','#skF_4','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_2'),u1_struct_0('#skF_3'))
    | r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',k4_tmap_1('#skF_2','#skF_3'))
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_58,c_93,c_78,c_377,c_56,c_54,c_52,c_1182,c_1200,c_1286])).

tff(c_1292,plain,(
    m1_subset_1('#skF_1'('#skF_3','#skF_4','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_2'),u1_struct_0('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_60,c_1245,c_1291])).

tff(c_14,plain,(
    ! [C_24,A_18,B_22] :
      ( m1_subset_1(C_24,u1_struct_0(A_18))
      | ~ m1_subset_1(C_24,u1_struct_0(B_22))
      | ~ m1_pre_topc(B_22,A_18)
      | v2_struct_0(B_22)
      | ~ l1_pre_topc(A_18)
      | v2_struct_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_1299,plain,(
    ! [A_18] :
      ( m1_subset_1('#skF_1'('#skF_3','#skF_4','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_2'),u1_struct_0(A_18))
      | ~ m1_pre_topc('#skF_3',A_18)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_18)
      | v2_struct_0(A_18) ) ),
    inference(resolution,[status(thm)],[c_1292,c_14])).

tff(c_1308,plain,(
    ! [A_391] :
      ( m1_subset_1('#skF_1'('#skF_3','#skF_4','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_2'),u1_struct_0(A_391))
      | ~ m1_pre_topc('#skF_3',A_391)
      | ~ l1_pre_topc(A_391)
      | v2_struct_0(A_391) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_1299])).

tff(c_1244,plain,(
    r2_hidden('#skF_1'('#skF_3','#skF_4','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_2'),u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1199])).

tff(c_50,plain,(
    ! [D_184] :
      ( k1_funct_1('#skF_4',D_184) = D_184
      | ~ r2_hidden(D_184,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(D_184,u1_struct_0('#skF_2')) ) ),
    inference(cnfTransformation,[status(thm)],[f_344])).

tff(c_1272,plain,
    ( k1_funct_1('#skF_4','#skF_1'('#skF_3','#skF_4','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_2')) = '#skF_1'('#skF_3','#skF_4','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_2')
    | ~ m1_subset_1('#skF_1'('#skF_3','#skF_4','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_2'),u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_1244,c_50])).

tff(c_1273,plain,(
    ~ m1_subset_1('#skF_1'('#skF_3','#skF_4','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_2'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_1272])).

tff(c_1314,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_1308,c_1273])).

tff(c_1322,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_58,c_1314])).

tff(c_1324,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_1322])).

tff(c_1326,plain,(
    m1_subset_1('#skF_1'('#skF_3','#skF_4','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_2'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_1272])).

tff(c_46,plain,(
    ! [A_166,B_170,C_172] :
      ( k1_funct_1(k4_tmap_1(A_166,B_170),C_172) = C_172
      | ~ r2_hidden(C_172,u1_struct_0(B_170))
      | ~ m1_subset_1(C_172,u1_struct_0(A_166))
      | ~ m1_pre_topc(B_170,A_166)
      | v2_struct_0(B_170)
      | ~ l1_pre_topc(A_166)
      | ~ v2_pre_topc(A_166)
      | v2_struct_0(A_166) ) ),
    inference(cnfTransformation,[status(thm)],[f_314])).

tff(c_1265,plain,(
    ! [A_166] :
      ( k1_funct_1(k4_tmap_1(A_166,'#skF_3'),'#skF_1'('#skF_3','#skF_4','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_2')) = '#skF_1'('#skF_3','#skF_4','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_2')
      | ~ m1_subset_1('#skF_1'('#skF_3','#skF_4','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_2'),u1_struct_0(A_166))
      | ~ m1_pre_topc('#skF_3',A_166)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_166)
      | ~ v2_pre_topc(A_166)
      | v2_struct_0(A_166) ) ),
    inference(resolution,[status(thm)],[c_1244,c_46])).

tff(c_1363,plain,(
    ! [A_395] :
      ( k1_funct_1(k4_tmap_1(A_395,'#skF_3'),'#skF_1'('#skF_3','#skF_4','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_2')) = '#skF_1'('#skF_3','#skF_4','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_2')
      | ~ m1_subset_1('#skF_1'('#skF_3','#skF_4','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_2'),u1_struct_0(A_395))
      | ~ m1_pre_topc('#skF_3',A_395)
      | ~ l1_pre_topc(A_395)
      | ~ v2_pre_topc(A_395)
      | v2_struct_0(A_395) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_1265])).

tff(c_1369,plain,
    ( k1_funct_1(k4_tmap_1('#skF_2','#skF_3'),'#skF_1'('#skF_3','#skF_4','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_2')) = '#skF_1'('#skF_3','#skF_4','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_2')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_1326,c_1363])).

tff(c_1373,plain,
    ( k1_funct_1(k4_tmap_1('#skF_2','#skF_3'),'#skF_1'('#skF_3','#skF_4','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_2')) = '#skF_1'('#skF_3','#skF_4','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_58,c_1369])).

tff(c_1374,plain,(
    k1_funct_1(k4_tmap_1('#skF_2','#skF_3'),'#skF_1'('#skF_3','#skF_4','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_2')) = '#skF_1'('#skF_3','#skF_4','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_1373])).

tff(c_277,plain,
    ( k3_tmap_1('#skF_3','#skF_2','#skF_3','#skF_3','#skF_4') = '#skF_4'
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_273])).

tff(c_283,plain,
    ( k3_tmap_1('#skF_3','#skF_2','#skF_3','#skF_3','#skF_4') = '#skF_4'
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_93,c_277])).

tff(c_284,plain,(
    k3_tmap_1('#skF_3','#skF_2','#skF_3','#skF_3','#skF_4') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_283])).

tff(c_1325,plain,(
    k1_funct_1('#skF_4','#skF_1'('#skF_3','#skF_4','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_2')) = '#skF_1'('#skF_3','#skF_4','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_1272])).

tff(c_363,plain,(
    ! [A_81] :
      ( k3_tmap_1(A_81,'#skF_2','#skF_3',A_81,'#skF_4') = k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',u1_struct_0(A_81))
      | ~ m1_pre_topc(A_81,'#skF_3')
      | ~ m1_pre_topc('#skF_3',A_81)
      | ~ v2_pre_topc(A_81)
      | v2_struct_0(A_81)
      | ~ l1_pre_topc(A_81) ) ),
    inference(resolution,[status(thm)],[c_34,c_358])).

tff(c_426,plain,(
    ! [A_290] :
      ( k3_tmap_1(A_290,'#skF_2','#skF_3',A_290,'#skF_4') = k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',u1_struct_0(A_290))
      | ~ m1_pre_topc(A_290,'#skF_3')
      | ~ m1_pre_topc('#skF_3',A_290)
      | ~ v2_pre_topc(A_290)
      | v2_struct_0(A_290)
      | ~ l1_pre_topc(A_290) ) ),
    inference(resolution,[status(thm)],[c_34,c_358])).

tff(c_438,plain,(
    ! [A_290] :
      ( m1_subset_1(k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',u1_struct_0(A_290)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_290),u1_struct_0('#skF_2'))))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_4')
      | ~ m1_pre_topc(A_290,A_290)
      | ~ m1_pre_topc('#skF_3',A_290)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_290)
      | ~ v2_pre_topc(A_290)
      | v2_struct_0(A_290)
      | ~ m1_pre_topc(A_290,'#skF_3')
      | ~ m1_pre_topc('#skF_3',A_290)
      | ~ v2_pre_topc(A_290)
      | v2_struct_0(A_290)
      | ~ l1_pre_topc(A_290) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_426,c_20])).

tff(c_466,plain,(
    ! [A_290] :
      ( m1_subset_1(k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',u1_struct_0(A_290)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_290),u1_struct_0('#skF_2'))))
      | ~ m1_pre_topc(A_290,A_290)
      | v2_struct_0('#skF_2')
      | ~ m1_pre_topc(A_290,'#skF_3')
      | ~ m1_pre_topc('#skF_3',A_290)
      | ~ v2_pre_topc(A_290)
      | v2_struct_0(A_290)
      | ~ l1_pre_topc(A_290) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_56,c_54,c_52,c_438])).

tff(c_500,plain,(
    ! [A_297] :
      ( m1_subset_1(k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',u1_struct_0(A_297)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_297),u1_struct_0('#skF_2'))))
      | ~ m1_pre_topc(A_297,A_297)
      | ~ m1_pre_topc(A_297,'#skF_3')
      | ~ m1_pre_topc('#skF_3',A_297)
      | ~ v2_pre_topc(A_297)
      | v2_struct_0(A_297)
      | ~ l1_pre_topc(A_297) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_466])).

tff(c_521,plain,(
    ! [A_81] :
      ( m1_subset_1(k3_tmap_1(A_81,'#skF_2','#skF_3',A_81,'#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_81),u1_struct_0('#skF_2'))))
      | ~ m1_pre_topc(A_81,A_81)
      | ~ m1_pre_topc(A_81,'#skF_3')
      | ~ m1_pre_topc('#skF_3',A_81)
      | ~ v2_pre_topc(A_81)
      | v2_struct_0(A_81)
      | ~ l1_pre_topc(A_81)
      | ~ m1_pre_topc(A_81,'#skF_3')
      | ~ m1_pre_topc('#skF_3',A_81)
      | ~ v2_pre_topc(A_81)
      | v2_struct_0(A_81)
      | ~ l1_pre_topc(A_81) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_363,c_500])).

tff(c_1375,plain,(
    ! [B_396,D_397,B_398,A_399] :
      ( m1_subset_1('#skF_1'(B_396,D_397,B_398,k4_tmap_1(A_399,B_398),A_399),u1_struct_0(B_396))
      | r2_funct_2(u1_struct_0(B_398),u1_struct_0(A_399),k2_tmap_1(B_396,A_399,D_397,B_398),k4_tmap_1(A_399,B_398))
      | ~ v1_funct_2(k4_tmap_1(A_399,B_398),u1_struct_0(B_398),u1_struct_0(A_399))
      | ~ v1_funct_1(k4_tmap_1(A_399,B_398))
      | ~ m1_subset_1(D_397,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_396),u1_struct_0(A_399))))
      | ~ v1_funct_2(D_397,u1_struct_0(B_396),u1_struct_0(A_399))
      | ~ v1_funct_1(D_397)
      | ~ m1_pre_topc(B_398,B_396)
      | v2_struct_0(B_398)
      | ~ l1_pre_topc(B_396)
      | ~ v2_pre_topc(B_396)
      | v2_struct_0(B_396)
      | ~ m1_pre_topc(B_398,A_399)
      | ~ l1_pre_topc(A_399)
      | ~ v2_pre_topc(A_399)
      | v2_struct_0(A_399) ) ),
    inference(resolution,[status(thm)],[c_26,c_676])).

tff(c_1386,plain,
    ( m1_subset_1('#skF_1'('#skF_3','#skF_4','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_2'),u1_struct_0('#skF_3'))
    | r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',k4_tmap_1('#skF_2','#skF_3'))
    | ~ v1_funct_2(k4_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k4_tmap_1('#skF_2','#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_416,c_1375])).

tff(c_1391,plain,
    ( m1_subset_1('#skF_1'('#skF_3','#skF_4','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_2'),u1_struct_0('#skF_3'))
    | r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',k4_tmap_1('#skF_2','#skF_3'))
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_58,c_93,c_78,c_377,c_56,c_54,c_52,c_1182,c_1200,c_1386])).

tff(c_1392,plain,(
    m1_subset_1('#skF_1'('#skF_3','#skF_4','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_2'),u1_struct_0('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_60,c_1245,c_1391])).

tff(c_4,plain,(
    ! [A_4,B_5,C_6,D_7] :
      ( k3_funct_2(A_4,B_5,C_6,D_7) = k1_funct_1(C_6,D_7)
      | ~ m1_subset_1(D_7,A_4)
      | ~ m1_subset_1(C_6,k1_zfmisc_1(k2_zfmisc_1(A_4,B_5)))
      | ~ v1_funct_2(C_6,A_4,B_5)
      | ~ v1_funct_1(C_6)
      | v1_xboole_0(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1404,plain,(
    ! [B_5,C_6] :
      ( k3_funct_2(u1_struct_0('#skF_3'),B_5,C_6,'#skF_1'('#skF_3','#skF_4','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_2')) = k1_funct_1(C_6,'#skF_1'('#skF_3','#skF_4','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_2'))
      | ~ m1_subset_1(C_6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),B_5)))
      | ~ v1_funct_2(C_6,u1_struct_0('#skF_3'),B_5)
      | ~ v1_funct_1(C_6)
      | v1_xboole_0(u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_1392,c_4])).

tff(c_1480,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1404])).

tff(c_94,plain,(
    ! [B_193,A_194] :
      ( m1_subset_1(u1_struct_0(B_193),k1_zfmisc_1(u1_struct_0(A_194)))
      | ~ m1_pre_topc(B_193,A_194)
      | ~ l1_pre_topc(A_194) ) ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_2,plain,(
    ! [C_3,B_2,A_1] :
      ( ~ v1_xboole_0(C_3)
      | ~ m1_subset_1(B_2,k1_zfmisc_1(C_3))
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_97,plain,(
    ! [A_194,A_1,B_193] :
      ( ~ v1_xboole_0(u1_struct_0(A_194))
      | ~ r2_hidden(A_1,u1_struct_0(B_193))
      | ~ m1_pre_topc(B_193,A_194)
      | ~ l1_pre_topc(A_194) ) ),
    inference(resolution,[status(thm)],[c_94,c_2])).

tff(c_1482,plain,(
    ! [A_1,B_193] :
      ( ~ r2_hidden(A_1,u1_struct_0(B_193))
      | ~ m1_pre_topc(B_193,'#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_1480,c_97])).

tff(c_1519,plain,(
    ! [A_411,B_412] :
      ( ~ r2_hidden(A_411,u1_struct_0(B_412))
      | ~ m1_pre_topc(B_412,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_1482])).

tff(c_1522,plain,(
    ~ m1_pre_topc('#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_1244,c_1519])).

tff(c_1526,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_377,c_1522])).

tff(c_1529,plain,(
    ! [B_413,C_414] :
      ( k3_funct_2(u1_struct_0('#skF_3'),B_413,C_414,'#skF_1'('#skF_3','#skF_4','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_2')) = k1_funct_1(C_414,'#skF_1'('#skF_3','#skF_4','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_2'))
      | ~ m1_subset_1(C_414,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),B_413)))
      | ~ v1_funct_2(C_414,u1_struct_0('#skF_3'),B_413)
      | ~ v1_funct_1(C_414) ) ),
    inference(splitRight,[status(thm)],[c_1404])).

tff(c_1533,plain,
    ( k3_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_3','#skF_2','#skF_3','#skF_3','#skF_4'),'#skF_1'('#skF_3','#skF_4','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_2')) = k1_funct_1(k3_tmap_1('#skF_3','#skF_2','#skF_3','#skF_3','#skF_4'),'#skF_1'('#skF_3','#skF_4','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_2'))
    | ~ v1_funct_2(k3_tmap_1('#skF_3','#skF_2','#skF_3','#skF_3','#skF_4'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k3_tmap_1('#skF_3','#skF_2','#skF_3','#skF_3','#skF_4'))
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_521,c_1529])).

tff(c_1555,plain,
    ( k3_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4','#skF_1'('#skF_3','#skF_4','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_2')) = '#skF_1'('#skF_3','#skF_4','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_2')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_93,c_377,c_56,c_284,c_54,c_284,c_1325,c_284,c_284,c_1533])).

tff(c_1556,plain,(
    k3_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4','#skF_1'('#skF_3','#skF_4','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_2')) = '#skF_1'('#skF_3','#skF_4','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_1555])).

tff(c_36,plain,(
    ! [D_138,A_82,B_114,C_130,E_142] :
      ( k3_funct_2(u1_struct_0(B_114),u1_struct_0(A_82),D_138,'#skF_1'(B_114,D_138,C_130,E_142,A_82)) != k1_funct_1(E_142,'#skF_1'(B_114,D_138,C_130,E_142,A_82))
      | r2_funct_2(u1_struct_0(C_130),u1_struct_0(A_82),k2_tmap_1(B_114,A_82,D_138,C_130),E_142)
      | ~ m1_subset_1(E_142,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_130),u1_struct_0(A_82))))
      | ~ v1_funct_2(E_142,u1_struct_0(C_130),u1_struct_0(A_82))
      | ~ v1_funct_1(E_142)
      | ~ m1_subset_1(D_138,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_114),u1_struct_0(A_82))))
      | ~ v1_funct_2(D_138,u1_struct_0(B_114),u1_struct_0(A_82))
      | ~ v1_funct_1(D_138)
      | ~ m1_pre_topc(C_130,B_114)
      | v2_struct_0(C_130)
      | ~ l1_pre_topc(B_114)
      | ~ v2_pre_topc(B_114)
      | v2_struct_0(B_114)
      | ~ l1_pre_topc(A_82)
      | ~ v2_pre_topc(A_82)
      | v2_struct_0(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_252])).

tff(c_1572,plain,
    ( k1_funct_1(k4_tmap_1('#skF_2','#skF_3'),'#skF_1'('#skF_3','#skF_4','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_2')) != '#skF_1'('#skF_3','#skF_4','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_2')
    | r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_3'),k4_tmap_1('#skF_2','#skF_3'))
    | ~ m1_subset_1(k4_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k4_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k4_tmap_1('#skF_2','#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1556,c_36])).

tff(c_1576,plain,
    ( r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',k4_tmap_1('#skF_2','#skF_3'))
    | ~ m1_subset_1(k4_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_93,c_78,c_377,c_56,c_54,c_52,c_1182,c_1200,c_416,c_1374,c_1572])).

tff(c_1577,plain,(
    ~ m1_subset_1(k4_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_60,c_1245,c_1576])).

tff(c_1581,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_1577])).

tff(c_1584,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_58,c_1581])).

tff(c_1586,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_1584])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n001.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 09:44:44 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.22/1.91  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.22/1.93  
% 5.22/1.93  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.31/1.93  %$ r2_funct_2 > v1_funct_2 > r2_hidden > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k3_funct_2 > k2_tmap_1 > k2_partfun1 > k4_tmap_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 5.31/1.93  
% 5.31/1.93  %Foreground sorts:
% 5.31/1.93  
% 5.31/1.93  
% 5.31/1.93  %Background operators:
% 5.31/1.93  
% 5.31/1.93  
% 5.31/1.93  %Foreground operators:
% 5.31/1.93  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.31/1.93  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 5.31/1.93  tff(k4_tmap_1, type, k4_tmap_1: ($i * $i) > $i).
% 5.31/1.93  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.31/1.93  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.31/1.93  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.31/1.93  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.31/1.93  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.31/1.93  tff('#skF_2', type, '#skF_2': $i).
% 5.31/1.93  tff('#skF_3', type, '#skF_3': $i).
% 5.31/1.93  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.31/1.93  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 5.31/1.93  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i) > $i).
% 5.31/1.93  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.31/1.93  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.31/1.93  tff('#skF_4', type, '#skF_4': $i).
% 5.31/1.93  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.31/1.93  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 5.31/1.93  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 5.31/1.93  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.31/1.93  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 5.31/1.93  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.31/1.93  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.31/1.93  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 5.31/1.93  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 5.31/1.93  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.31/1.93  
% 5.31/1.96  tff(f_344, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => ((![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, u1_struct_0(B)) => (D = k1_funct_1(C, D))))) => r2_funct_2(u1_struct_0(B), u1_struct_0(A), k4_tmap_1(A, B), C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t96_tmap_1)).
% 5.31/1.96  tff(f_197, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_pre_topc(B, A)) => ((v1_funct_1(k4_tmap_1(A, B)) & v1_funct_2(k4_tmap_1(A, B), u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(k4_tmap_1(A, B), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_tmap_1)).
% 5.31/1.96  tff(f_61, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_funct_2(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_funct_2)).
% 5.31/1.96  tff(f_70, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_pre_topc)).
% 5.31/1.96  tff(f_77, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 5.31/1.96  tff(f_208, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tsep_1)).
% 5.31/1.96  tff(f_182, axiom, (![A, B, C, D, E]: (((((((((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & ~v2_struct_0(B)) & v2_pre_topc(B)) & l1_pre_topc(B)) & m1_pre_topc(C, A)) & m1_pre_topc(D, A)) & v1_funct_1(E)) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => ((v1_funct_1(k3_tmap_1(A, B, C, D, E)) & v1_funct_2(k3_tmap_1(A, B, C, D, E), u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(k3_tmap_1(A, B, C, D, E), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_tmap_1)).
% 5.31/1.96  tff(f_282, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => r2_funct_2(u1_struct_0(C), u1_struct_0(B), D, k3_tmap_1(A, B, C, C, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_tmap_1)).
% 5.31/1.96  tff(f_152, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (m1_pre_topc(C, A) => (![D]: (m1_pre_topc(D, A) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (m1_pre_topc(D, C) => (k3_tmap_1(A, B, C, D, E) = k2_partfun1(u1_struct_0(C), u1_struct_0(B), E, u1_struct_0(D)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tmap_1)).
% 5.31/1.96  tff(f_120, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tmap_1)).
% 5.31/1.96  tff(f_252, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, B)) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(A))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(A))))) => ((![F]: (m1_subset_1(F, u1_struct_0(B)) => (r2_hidden(F, u1_struct_0(C)) => (k3_funct_2(u1_struct_0(B), u1_struct_0(A), D, F) = k1_funct_1(E, F))))) => r2_funct_2(u1_struct_0(C), u1_struct_0(A), k2_tmap_1(B, A, D, C), E)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_tmap_1)).
% 5.31/1.96  tff(f_93, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(B)) => m1_subset_1(C, u1_struct_0(A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_pre_topc)).
% 5.31/1.96  tff(f_314, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(C, u1_struct_0(B)) => (k1_funct_1(k4_tmap_1(A, B), C) = C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_tmap_1)).
% 5.31/1.96  tff(f_45, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => (k3_funct_2(A, B, C, D) = k1_funct_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 5.31/1.96  tff(f_204, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 5.31/1.96  tff(f_32, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 5.31/1.96  tff(c_66, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_344])).
% 5.31/1.96  tff(c_64, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_344])).
% 5.31/1.96  tff(c_62, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_344])).
% 5.31/1.96  tff(c_58, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_344])).
% 5.31/1.96  tff(c_26, plain, (![A_76, B_77]: (m1_subset_1(k4_tmap_1(A_76, B_77), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_77), u1_struct_0(A_76)))) | ~m1_pre_topc(B_77, A_76) | ~l1_pre_topc(A_76) | ~v2_pre_topc(A_76) | v2_struct_0(A_76))), inference(cnfTransformation, [status(thm)], [f_197])).
% 5.31/1.96  tff(c_60, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_344])).
% 5.31/1.96  tff(c_56, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_344])).
% 5.31/1.96  tff(c_54, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_344])).
% 5.31/1.96  tff(c_52, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_344])).
% 5.31/1.96  tff(c_117, plain, (![A_205, B_206, D_207]: (r2_funct_2(A_205, B_206, D_207, D_207) | ~m1_subset_1(D_207, k1_zfmisc_1(k2_zfmisc_1(A_205, B_206))) | ~v1_funct_2(D_207, A_205, B_206) | ~v1_funct_1(D_207))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.31/1.96  tff(c_119, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', '#skF_4') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_52, c_117])).
% 5.31/1.96  tff(c_122, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_119])).
% 5.31/1.96  tff(c_30, plain, (![A_76, B_77]: (v1_funct_1(k4_tmap_1(A_76, B_77)) | ~m1_pre_topc(B_77, A_76) | ~l1_pre_topc(A_76) | ~v2_pre_topc(A_76) | v2_struct_0(A_76))), inference(cnfTransformation, [status(thm)], [f_197])).
% 5.31/1.96  tff(c_83, plain, (![B_191, A_192]: (v2_pre_topc(B_191) | ~m1_pre_topc(B_191, A_192) | ~l1_pre_topc(A_192) | ~v2_pre_topc(A_192))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.31/1.96  tff(c_89, plain, (v2_pre_topc('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_58, c_83])).
% 5.31/1.96  tff(c_93, plain, (v2_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_89])).
% 5.31/1.96  tff(c_68, plain, (![B_186, A_187]: (l1_pre_topc(B_186) | ~m1_pre_topc(B_186, A_187) | ~l1_pre_topc(A_187))), inference(cnfTransformation, [status(thm)], [f_77])).
% 5.31/1.96  tff(c_74, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_58, c_68])).
% 5.31/1.96  tff(c_78, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_74])).
% 5.31/1.96  tff(c_34, plain, (![A_81]: (m1_pre_topc(A_81, A_81) | ~l1_pre_topc(A_81))), inference(cnfTransformation, [status(thm)], [f_208])).
% 5.31/1.96  tff(c_157, plain, (![B_237, D_238, E_235, C_239, A_236]: (v1_funct_1(k3_tmap_1(A_236, B_237, C_239, D_238, E_235)) | ~m1_subset_1(E_235, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_239), u1_struct_0(B_237)))) | ~v1_funct_2(E_235, u1_struct_0(C_239), u1_struct_0(B_237)) | ~v1_funct_1(E_235) | ~m1_pre_topc(D_238, A_236) | ~m1_pre_topc(C_239, A_236) | ~l1_pre_topc(B_237) | ~v2_pre_topc(B_237) | v2_struct_0(B_237) | ~l1_pre_topc(A_236) | ~v2_pre_topc(A_236) | v2_struct_0(A_236))), inference(cnfTransformation, [status(thm)], [f_182])).
% 5.31/1.96  tff(c_161, plain, (![A_236, D_238]: (v1_funct_1(k3_tmap_1(A_236, '#skF_2', '#skF_3', D_238, '#skF_4')) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~m1_pre_topc(D_238, A_236) | ~m1_pre_topc('#skF_3', A_236) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_236) | ~v2_pre_topc(A_236) | v2_struct_0(A_236))), inference(resolution, [status(thm)], [c_52, c_157])).
% 5.31/1.96  tff(c_165, plain, (![A_236, D_238]: (v1_funct_1(k3_tmap_1(A_236, '#skF_2', '#skF_3', D_238, '#skF_4')) | ~m1_pre_topc(D_238, A_236) | ~m1_pre_topc('#skF_3', A_236) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_236) | ~v2_pre_topc(A_236) | v2_struct_0(A_236))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_56, c_54, c_161])).
% 5.31/1.96  tff(c_166, plain, (![A_236, D_238]: (v1_funct_1(k3_tmap_1(A_236, '#skF_2', '#skF_3', D_238, '#skF_4')) | ~m1_pre_topc(D_238, A_236) | ~m1_pre_topc('#skF_3', A_236) | ~l1_pre_topc(A_236) | ~v2_pre_topc(A_236) | v2_struct_0(A_236))), inference(negUnitSimplification, [status(thm)], [c_66, c_165])).
% 5.31/1.96  tff(c_193, plain, (![E_255, C_259, A_256, D_258, B_257]: (v1_funct_2(k3_tmap_1(A_256, B_257, C_259, D_258, E_255), u1_struct_0(D_258), u1_struct_0(B_257)) | ~m1_subset_1(E_255, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_259), u1_struct_0(B_257)))) | ~v1_funct_2(E_255, u1_struct_0(C_259), u1_struct_0(B_257)) | ~v1_funct_1(E_255) | ~m1_pre_topc(D_258, A_256) | ~m1_pre_topc(C_259, A_256) | ~l1_pre_topc(B_257) | ~v2_pre_topc(B_257) | v2_struct_0(B_257) | ~l1_pre_topc(A_256) | ~v2_pre_topc(A_256) | v2_struct_0(A_256))), inference(cnfTransformation, [status(thm)], [f_182])).
% 5.31/1.96  tff(c_197, plain, (![A_256, D_258]: (v1_funct_2(k3_tmap_1(A_256, '#skF_2', '#skF_3', D_258, '#skF_4'), u1_struct_0(D_258), u1_struct_0('#skF_2')) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~m1_pre_topc(D_258, A_256) | ~m1_pre_topc('#skF_3', A_256) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_256) | ~v2_pre_topc(A_256) | v2_struct_0(A_256))), inference(resolution, [status(thm)], [c_52, c_193])).
% 5.31/1.96  tff(c_201, plain, (![A_256, D_258]: (v1_funct_2(k3_tmap_1(A_256, '#skF_2', '#skF_3', D_258, '#skF_4'), u1_struct_0(D_258), u1_struct_0('#skF_2')) | ~m1_pre_topc(D_258, A_256) | ~m1_pre_topc('#skF_3', A_256) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_256) | ~v2_pre_topc(A_256) | v2_struct_0(A_256))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_56, c_54, c_197])).
% 5.31/1.96  tff(c_202, plain, (![A_256, D_258]: (v1_funct_2(k3_tmap_1(A_256, '#skF_2', '#skF_3', D_258, '#skF_4'), u1_struct_0(D_258), u1_struct_0('#skF_2')) | ~m1_pre_topc(D_258, A_256) | ~m1_pre_topc('#skF_3', A_256) | ~l1_pre_topc(A_256) | ~v2_pre_topc(A_256) | v2_struct_0(A_256))), inference(negUnitSimplification, [status(thm)], [c_66, c_201])).
% 5.31/1.96  tff(c_20, plain, (![D_74, C_73, B_72, E_75, A_71]: (m1_subset_1(k3_tmap_1(A_71, B_72, C_73, D_74, E_75), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_74), u1_struct_0(B_72)))) | ~m1_subset_1(E_75, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_73), u1_struct_0(B_72)))) | ~v1_funct_2(E_75, u1_struct_0(C_73), u1_struct_0(B_72)) | ~v1_funct_1(E_75) | ~m1_pre_topc(D_74, A_71) | ~m1_pre_topc(C_73, A_71) | ~l1_pre_topc(B_72) | ~v2_pre_topc(B_72) | v2_struct_0(B_72) | ~l1_pre_topc(A_71) | ~v2_pre_topc(A_71) | v2_struct_0(A_71))), inference(cnfTransformation, [status(thm)], [f_182])).
% 5.31/1.96  tff(c_204, plain, (![C_262, B_263, D_264, A_265]: (r2_funct_2(u1_struct_0(C_262), u1_struct_0(B_263), D_264, k3_tmap_1(A_265, B_263, C_262, C_262, D_264)) | ~m1_subset_1(D_264, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_262), u1_struct_0(B_263)))) | ~v1_funct_2(D_264, u1_struct_0(C_262), u1_struct_0(B_263)) | ~v1_funct_1(D_264) | ~m1_pre_topc(C_262, A_265) | v2_struct_0(C_262) | ~l1_pre_topc(B_263) | ~v2_pre_topc(B_263) | v2_struct_0(B_263) | ~l1_pre_topc(A_265) | ~v2_pre_topc(A_265) | v2_struct_0(A_265))), inference(cnfTransformation, [status(thm)], [f_282])).
% 5.31/1.96  tff(c_208, plain, (![A_265]: (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', k3_tmap_1(A_265, '#skF_2', '#skF_3', '#skF_3', '#skF_4')) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~m1_pre_topc('#skF_3', A_265) | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_265) | ~v2_pre_topc(A_265) | v2_struct_0(A_265))), inference(resolution, [status(thm)], [c_52, c_204])).
% 5.31/1.96  tff(c_212, plain, (![A_265]: (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', k3_tmap_1(A_265, '#skF_2', '#skF_3', '#skF_3', '#skF_4')) | ~m1_pre_topc('#skF_3', A_265) | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_265) | ~v2_pre_topc(A_265) | v2_struct_0(A_265))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_56, c_54, c_208])).
% 5.31/1.96  tff(c_236, plain, (![A_271]: (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', k3_tmap_1(A_271, '#skF_2', '#skF_3', '#skF_3', '#skF_4')) | ~m1_pre_topc('#skF_3', A_271) | ~l1_pre_topc(A_271) | ~v2_pre_topc(A_271) | v2_struct_0(A_271))), inference(negUnitSimplification, [status(thm)], [c_66, c_60, c_212])).
% 5.31/1.96  tff(c_8, plain, (![D_11, C_10, A_8, B_9]: (D_11=C_10 | ~r2_funct_2(A_8, B_9, C_10, D_11) | ~m1_subset_1(D_11, k1_zfmisc_1(k2_zfmisc_1(A_8, B_9))) | ~v1_funct_2(D_11, A_8, B_9) | ~v1_funct_1(D_11) | ~m1_subset_1(C_10, k1_zfmisc_1(k2_zfmisc_1(A_8, B_9))) | ~v1_funct_2(C_10, A_8, B_9) | ~v1_funct_1(C_10))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.31/1.96  tff(c_238, plain, (![A_271]: (k3_tmap_1(A_271, '#skF_2', '#skF_3', '#skF_3', '#skF_4')='#skF_4' | ~m1_subset_1(k3_tmap_1(A_271, '#skF_2', '#skF_3', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k3_tmap_1(A_271, '#skF_2', '#skF_3', '#skF_3', '#skF_4'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1(A_271, '#skF_2', '#skF_3', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~m1_pre_topc('#skF_3', A_271) | ~l1_pre_topc(A_271) | ~v2_pre_topc(A_271) | v2_struct_0(A_271))), inference(resolution, [status(thm)], [c_236, c_8])).
% 5.31/1.96  tff(c_252, plain, (![A_279]: (k3_tmap_1(A_279, '#skF_2', '#skF_3', '#skF_3', '#skF_4')='#skF_4' | ~m1_subset_1(k3_tmap_1(A_279, '#skF_2', '#skF_3', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k3_tmap_1(A_279, '#skF_2', '#skF_3', '#skF_3', '#skF_4'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1(A_279, '#skF_2', '#skF_3', '#skF_3', '#skF_4')) | ~m1_pre_topc('#skF_3', A_279) | ~l1_pre_topc(A_279) | ~v2_pre_topc(A_279) | v2_struct_0(A_279))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_238])).
% 5.31/1.96  tff(c_256, plain, (![A_71]: (k3_tmap_1(A_71, '#skF_2', '#skF_3', '#skF_3', '#skF_4')='#skF_4' | ~v1_funct_2(k3_tmap_1(A_71, '#skF_2', '#skF_3', '#skF_3', '#skF_4'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1(A_71, '#skF_2', '#skF_3', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~m1_pre_topc('#skF_3', A_71) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_71) | ~v2_pre_topc(A_71) | v2_struct_0(A_71))), inference(resolution, [status(thm)], [c_20, c_252])).
% 5.31/1.96  tff(c_259, plain, (![A_71]: (k3_tmap_1(A_71, '#skF_2', '#skF_3', '#skF_3', '#skF_4')='#skF_4' | ~v1_funct_2(k3_tmap_1(A_71, '#skF_2', '#skF_3', '#skF_3', '#skF_4'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1(A_71, '#skF_2', '#skF_3', '#skF_3', '#skF_4')) | ~m1_pre_topc('#skF_3', A_71) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_71) | ~v2_pre_topc(A_71) | v2_struct_0(A_71))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_56, c_54, c_52, c_256])).
% 5.31/1.96  tff(c_261, plain, (![A_280]: (k3_tmap_1(A_280, '#skF_2', '#skF_3', '#skF_3', '#skF_4')='#skF_4' | ~v1_funct_2(k3_tmap_1(A_280, '#skF_2', '#skF_3', '#skF_3', '#skF_4'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1(A_280, '#skF_2', '#skF_3', '#skF_3', '#skF_4')) | ~m1_pre_topc('#skF_3', A_280) | ~l1_pre_topc(A_280) | ~v2_pre_topc(A_280) | v2_struct_0(A_280))), inference(negUnitSimplification, [status(thm)], [c_66, c_259])).
% 5.31/1.96  tff(c_267, plain, (![A_281]: (k3_tmap_1(A_281, '#skF_2', '#skF_3', '#skF_3', '#skF_4')='#skF_4' | ~v1_funct_1(k3_tmap_1(A_281, '#skF_2', '#skF_3', '#skF_3', '#skF_4')) | ~m1_pre_topc('#skF_3', A_281) | ~l1_pre_topc(A_281) | ~v2_pre_topc(A_281) | v2_struct_0(A_281))), inference(resolution, [status(thm)], [c_202, c_261])).
% 5.31/1.96  tff(c_273, plain, (![A_282]: (k3_tmap_1(A_282, '#skF_2', '#skF_3', '#skF_3', '#skF_4')='#skF_4' | ~m1_pre_topc('#skF_3', A_282) | ~l1_pre_topc(A_282) | ~v2_pre_topc(A_282) | v2_struct_0(A_282))), inference(resolution, [status(thm)], [c_166, c_267])).
% 5.31/1.96  tff(c_280, plain, (k3_tmap_1('#skF_2', '#skF_2', '#skF_3', '#skF_3', '#skF_4')='#skF_4' | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_58, c_273])).
% 5.31/1.96  tff(c_287, plain, (k3_tmap_1('#skF_2', '#skF_2', '#skF_3', '#skF_3', '#skF_4')='#skF_4' | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_280])).
% 5.31/1.96  tff(c_288, plain, (k3_tmap_1('#skF_2', '#skF_2', '#skF_3', '#skF_3', '#skF_4')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_66, c_287])).
% 5.31/1.96  tff(c_345, plain, (![C_285, E_287, A_284, B_283, D_286]: (k3_tmap_1(A_284, B_283, C_285, D_286, E_287)=k2_partfun1(u1_struct_0(C_285), u1_struct_0(B_283), E_287, u1_struct_0(D_286)) | ~m1_pre_topc(D_286, C_285) | ~m1_subset_1(E_287, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_285), u1_struct_0(B_283)))) | ~v1_funct_2(E_287, u1_struct_0(C_285), u1_struct_0(B_283)) | ~v1_funct_1(E_287) | ~m1_pre_topc(D_286, A_284) | ~m1_pre_topc(C_285, A_284) | ~l1_pre_topc(B_283) | ~v2_pre_topc(B_283) | v2_struct_0(B_283) | ~l1_pre_topc(A_284) | ~v2_pre_topc(A_284) | v2_struct_0(A_284))), inference(cnfTransformation, [status(thm)], [f_152])).
% 5.31/1.96  tff(c_351, plain, (![A_284, D_286]: (k3_tmap_1(A_284, '#skF_2', '#skF_3', D_286, '#skF_4')=k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', u1_struct_0(D_286)) | ~m1_pre_topc(D_286, '#skF_3') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~m1_pre_topc(D_286, A_284) | ~m1_pre_topc('#skF_3', A_284) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_284) | ~v2_pre_topc(A_284) | v2_struct_0(A_284))), inference(resolution, [status(thm)], [c_52, c_345])).
% 5.31/1.96  tff(c_356, plain, (![A_284, D_286]: (k3_tmap_1(A_284, '#skF_2', '#skF_3', D_286, '#skF_4')=k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', u1_struct_0(D_286)) | ~m1_pre_topc(D_286, '#skF_3') | ~m1_pre_topc(D_286, A_284) | ~m1_pre_topc('#skF_3', A_284) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_284) | ~v2_pre_topc(A_284) | v2_struct_0(A_284))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_56, c_54, c_351])).
% 5.31/1.96  tff(c_358, plain, (![A_288, D_289]: (k3_tmap_1(A_288, '#skF_2', '#skF_3', D_289, '#skF_4')=k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', u1_struct_0(D_289)) | ~m1_pre_topc(D_289, '#skF_3') | ~m1_pre_topc(D_289, A_288) | ~m1_pre_topc('#skF_3', A_288) | ~l1_pre_topc(A_288) | ~v2_pre_topc(A_288) | v2_struct_0(A_288))), inference(negUnitSimplification, [status(thm)], [c_66, c_356])).
% 5.31/1.96  tff(c_362, plain, (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_2', '#skF_2', '#skF_3', '#skF_3', '#skF_4') | ~m1_pre_topc('#skF_3', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_58, c_358])).
% 5.31/1.96  tff(c_366, plain, (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', u1_struct_0('#skF_3'))='#skF_4' | ~m1_pre_topc('#skF_3', '#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_58, c_288, c_362])).
% 5.31/1.96  tff(c_367, plain, (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', u1_struct_0('#skF_3'))='#skF_4' | ~m1_pre_topc('#skF_3', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_66, c_366])).
% 5.31/1.96  tff(c_368, plain, (~m1_pre_topc('#skF_3', '#skF_3')), inference(splitLeft, [status(thm)], [c_367])).
% 5.31/1.96  tff(c_371, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_34, c_368])).
% 5.31/1.96  tff(c_375, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_78, c_371])).
% 5.31/1.96  tff(c_377, plain, (m1_pre_topc('#skF_3', '#skF_3')), inference(splitRight, [status(thm)], [c_367])).
% 5.31/1.96  tff(c_376, plain, (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', u1_struct_0('#skF_3'))='#skF_4'), inference(splitRight, [status(thm)], [c_367])).
% 5.31/1.96  tff(c_167, plain, (![A_240, B_241, C_242, D_243]: (k2_partfun1(u1_struct_0(A_240), u1_struct_0(B_241), C_242, u1_struct_0(D_243))=k2_tmap_1(A_240, B_241, C_242, D_243) | ~m1_pre_topc(D_243, A_240) | ~m1_subset_1(C_242, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_240), u1_struct_0(B_241)))) | ~v1_funct_2(C_242, u1_struct_0(A_240), u1_struct_0(B_241)) | ~v1_funct_1(C_242) | ~l1_pre_topc(B_241) | ~v2_pre_topc(B_241) | v2_struct_0(B_241) | ~l1_pre_topc(A_240) | ~v2_pre_topc(A_240) | v2_struct_0(A_240))), inference(cnfTransformation, [status(thm)], [f_120])).
% 5.31/1.96  tff(c_171, plain, (![D_243]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', u1_struct_0(D_243))=k2_tmap_1('#skF_3', '#skF_2', '#skF_4', D_243) | ~m1_pre_topc(D_243, '#skF_3') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_52, c_167])).
% 5.31/1.96  tff(c_175, plain, (![D_243]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', u1_struct_0(D_243))=k2_tmap_1('#skF_3', '#skF_2', '#skF_4', D_243) | ~m1_pre_topc(D_243, '#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_93, c_78, c_64, c_62, c_56, c_54, c_171])).
% 5.31/1.96  tff(c_176, plain, (![D_243]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', u1_struct_0(D_243))=k2_tmap_1('#skF_3', '#skF_2', '#skF_4', D_243) | ~m1_pre_topc(D_243, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_60, c_66, c_175])).
% 5.31/1.96  tff(c_409, plain, (k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_3')='#skF_4' | ~m1_pre_topc('#skF_3', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_376, c_176])).
% 5.31/1.96  tff(c_416, plain, (k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_377, c_409])).
% 5.31/1.96  tff(c_473, plain, (![C_293, B_291, A_295, E_294, D_292]: (r2_hidden('#skF_1'(B_291, D_292, C_293, E_294, A_295), u1_struct_0(C_293)) | r2_funct_2(u1_struct_0(C_293), u1_struct_0(A_295), k2_tmap_1(B_291, A_295, D_292, C_293), E_294) | ~m1_subset_1(E_294, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_293), u1_struct_0(A_295)))) | ~v1_funct_2(E_294, u1_struct_0(C_293), u1_struct_0(A_295)) | ~v1_funct_1(E_294) | ~m1_subset_1(D_292, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_291), u1_struct_0(A_295)))) | ~v1_funct_2(D_292, u1_struct_0(B_291), u1_struct_0(A_295)) | ~v1_funct_1(D_292) | ~m1_pre_topc(C_293, B_291) | v2_struct_0(C_293) | ~l1_pre_topc(B_291) | ~v2_pre_topc(B_291) | v2_struct_0(B_291) | ~l1_pre_topc(A_295) | ~v2_pre_topc(A_295) | v2_struct_0(A_295))), inference(cnfTransformation, [status(thm)], [f_252])).
% 5.31/1.96  tff(c_1162, plain, (![B_373, D_374, B_375, A_376]: (r2_hidden('#skF_1'(B_373, D_374, B_375, k4_tmap_1(A_376, B_375), A_376), u1_struct_0(B_375)) | r2_funct_2(u1_struct_0(B_375), u1_struct_0(A_376), k2_tmap_1(B_373, A_376, D_374, B_375), k4_tmap_1(A_376, B_375)) | ~v1_funct_2(k4_tmap_1(A_376, B_375), u1_struct_0(B_375), u1_struct_0(A_376)) | ~v1_funct_1(k4_tmap_1(A_376, B_375)) | ~m1_subset_1(D_374, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_373), u1_struct_0(A_376)))) | ~v1_funct_2(D_374, u1_struct_0(B_373), u1_struct_0(A_376)) | ~v1_funct_1(D_374) | ~m1_pre_topc(B_375, B_373) | v2_struct_0(B_375) | ~l1_pre_topc(B_373) | ~v2_pre_topc(B_373) | v2_struct_0(B_373) | ~m1_pre_topc(B_375, A_376) | ~l1_pre_topc(A_376) | ~v2_pre_topc(A_376) | v2_struct_0(A_376))), inference(resolution, [status(thm)], [c_26, c_473])).
% 5.31/1.96  tff(c_1167, plain, (r2_hidden('#skF_1'('#skF_3', '#skF_4', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_2'), u1_struct_0('#skF_3')) | r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', k4_tmap_1('#skF_2', '#skF_3')) | ~v1_funct_2(k4_tmap_1('#skF_2', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k4_tmap_1('#skF_2', '#skF_3')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_416, c_1162])).
% 5.31/1.96  tff(c_1170, plain, (r2_hidden('#skF_1'('#skF_3', '#skF_4', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_2'), u1_struct_0('#skF_3')) | r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', k4_tmap_1('#skF_2', '#skF_3')) | ~v1_funct_2(k4_tmap_1('#skF_2', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k4_tmap_1('#skF_2', '#skF_3')) | v2_struct_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_58, c_93, c_78, c_377, c_56, c_54, c_52, c_1167])).
% 5.31/1.96  tff(c_1171, plain, (r2_hidden('#skF_1'('#skF_3', '#skF_4', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_2'), u1_struct_0('#skF_3')) | r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', k4_tmap_1('#skF_2', '#skF_3')) | ~v1_funct_2(k4_tmap_1('#skF_2', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k4_tmap_1('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_66, c_60, c_1170])).
% 5.31/1.96  tff(c_1172, plain, (~v1_funct_1(k4_tmap_1('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_1171])).
% 5.31/1.96  tff(c_1175, plain, (~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_30, c_1172])).
% 5.31/1.96  tff(c_1178, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_58, c_1175])).
% 5.31/1.96  tff(c_1180, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_1178])).
% 5.31/1.96  tff(c_1182, plain, (v1_funct_1(k4_tmap_1('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_1171])).
% 5.31/1.96  tff(c_28, plain, (![A_76, B_77]: (v1_funct_2(k4_tmap_1(A_76, B_77), u1_struct_0(B_77), u1_struct_0(A_76)) | ~m1_pre_topc(B_77, A_76) | ~l1_pre_topc(A_76) | ~v2_pre_topc(A_76) | v2_struct_0(A_76))), inference(cnfTransformation, [status(thm)], [f_197])).
% 5.31/1.96  tff(c_1181, plain, (~v1_funct_2(k4_tmap_1('#skF_2', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', k4_tmap_1('#skF_2', '#skF_3')) | r2_hidden('#skF_1'('#skF_3', '#skF_4', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_2'), u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_1171])).
% 5.31/1.96  tff(c_1190, plain, (~v1_funct_2(k4_tmap_1('#skF_2', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_1181])).
% 5.31/1.96  tff(c_1193, plain, (~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_28, c_1190])).
% 5.31/1.96  tff(c_1196, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_58, c_1193])).
% 5.31/1.96  tff(c_1198, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_1196])).
% 5.31/1.96  tff(c_1200, plain, (v1_funct_2(k4_tmap_1('#skF_2', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_1181])).
% 5.31/1.96  tff(c_1199, plain, (r2_hidden('#skF_1'('#skF_3', '#skF_4', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_2'), u1_struct_0('#skF_3')) | r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', k4_tmap_1('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_1181])).
% 5.31/1.96  tff(c_1201, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', k4_tmap_1('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_1199])).
% 5.31/1.96  tff(c_1203, plain, (k4_tmap_1('#skF_2', '#skF_3')='#skF_4' | ~m1_subset_1(k4_tmap_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k4_tmap_1('#skF_2', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k4_tmap_1('#skF_2', '#skF_3')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_1201, c_8])).
% 5.31/1.96  tff(c_1206, plain, (k4_tmap_1('#skF_2', '#skF_3')='#skF_4' | ~m1_subset_1(k4_tmap_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_1182, c_1200, c_1203])).
% 5.31/1.96  tff(c_1223, plain, (~m1_subset_1(k4_tmap_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(splitLeft, [status(thm)], [c_1206])).
% 5.31/1.96  tff(c_1226, plain, (~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_26, c_1223])).
% 5.31/1.96  tff(c_1229, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_58, c_1226])).
% 5.31/1.96  tff(c_1231, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_1229])).
% 5.31/1.96  tff(c_1232, plain, (k4_tmap_1('#skF_2', '#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_1206])).
% 5.31/1.96  tff(c_48, plain, (~r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k4_tmap_1('#skF_2', '#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_344])).
% 5.31/1.96  tff(c_1237, plain, (~r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1232, c_48])).
% 5.31/1.96  tff(c_1243, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_122, c_1237])).
% 5.31/1.96  tff(c_1245, plain, (~r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', k4_tmap_1('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_1199])).
% 5.31/1.96  tff(c_676, plain, (![B_307, D_308, A_311, E_310, C_309]: (m1_subset_1('#skF_1'(B_307, D_308, C_309, E_310, A_311), u1_struct_0(B_307)) | r2_funct_2(u1_struct_0(C_309), u1_struct_0(A_311), k2_tmap_1(B_307, A_311, D_308, C_309), E_310) | ~m1_subset_1(E_310, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_309), u1_struct_0(A_311)))) | ~v1_funct_2(E_310, u1_struct_0(C_309), u1_struct_0(A_311)) | ~v1_funct_1(E_310) | ~m1_subset_1(D_308, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_307), u1_struct_0(A_311)))) | ~v1_funct_2(D_308, u1_struct_0(B_307), u1_struct_0(A_311)) | ~v1_funct_1(D_308) | ~m1_pre_topc(C_309, B_307) | v2_struct_0(C_309) | ~l1_pre_topc(B_307) | ~v2_pre_topc(B_307) | v2_struct_0(B_307) | ~l1_pre_topc(A_311) | ~v2_pre_topc(A_311) | v2_struct_0(A_311))), inference(cnfTransformation, [status(thm)], [f_252])).
% 5.31/1.96  tff(c_1275, plain, (![B_387, D_388, B_389, A_390]: (m1_subset_1('#skF_1'(B_387, D_388, B_389, k4_tmap_1(A_390, B_389), A_390), u1_struct_0(B_387)) | r2_funct_2(u1_struct_0(B_389), u1_struct_0(A_390), k2_tmap_1(B_387, A_390, D_388, B_389), k4_tmap_1(A_390, B_389)) | ~v1_funct_2(k4_tmap_1(A_390, B_389), u1_struct_0(B_389), u1_struct_0(A_390)) | ~v1_funct_1(k4_tmap_1(A_390, B_389)) | ~m1_subset_1(D_388, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_387), u1_struct_0(A_390)))) | ~v1_funct_2(D_388, u1_struct_0(B_387), u1_struct_0(A_390)) | ~v1_funct_1(D_388) | ~m1_pre_topc(B_389, B_387) | v2_struct_0(B_389) | ~l1_pre_topc(B_387) | ~v2_pre_topc(B_387) | v2_struct_0(B_387) | ~m1_pre_topc(B_389, A_390) | ~l1_pre_topc(A_390) | ~v2_pre_topc(A_390) | v2_struct_0(A_390))), inference(resolution, [status(thm)], [c_26, c_676])).
% 5.31/1.96  tff(c_1286, plain, (m1_subset_1('#skF_1'('#skF_3', '#skF_4', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_2'), u1_struct_0('#skF_3')) | r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', k4_tmap_1('#skF_2', '#skF_3')) | ~v1_funct_2(k4_tmap_1('#skF_2', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k4_tmap_1('#skF_2', '#skF_3')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_416, c_1275])).
% 5.31/1.96  tff(c_1291, plain, (m1_subset_1('#skF_1'('#skF_3', '#skF_4', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_2'), u1_struct_0('#skF_3')) | r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', k4_tmap_1('#skF_2', '#skF_3')) | v2_struct_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_58, c_93, c_78, c_377, c_56, c_54, c_52, c_1182, c_1200, c_1286])).
% 5.31/1.96  tff(c_1292, plain, (m1_subset_1('#skF_1'('#skF_3', '#skF_4', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_2'), u1_struct_0('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_66, c_60, c_1245, c_1291])).
% 5.31/1.96  tff(c_14, plain, (![C_24, A_18, B_22]: (m1_subset_1(C_24, u1_struct_0(A_18)) | ~m1_subset_1(C_24, u1_struct_0(B_22)) | ~m1_pre_topc(B_22, A_18) | v2_struct_0(B_22) | ~l1_pre_topc(A_18) | v2_struct_0(A_18))), inference(cnfTransformation, [status(thm)], [f_93])).
% 5.31/1.96  tff(c_1299, plain, (![A_18]: (m1_subset_1('#skF_1'('#skF_3', '#skF_4', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_2'), u1_struct_0(A_18)) | ~m1_pre_topc('#skF_3', A_18) | v2_struct_0('#skF_3') | ~l1_pre_topc(A_18) | v2_struct_0(A_18))), inference(resolution, [status(thm)], [c_1292, c_14])).
% 5.31/1.96  tff(c_1308, plain, (![A_391]: (m1_subset_1('#skF_1'('#skF_3', '#skF_4', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_2'), u1_struct_0(A_391)) | ~m1_pre_topc('#skF_3', A_391) | ~l1_pre_topc(A_391) | v2_struct_0(A_391))), inference(negUnitSimplification, [status(thm)], [c_60, c_1299])).
% 5.31/1.96  tff(c_1244, plain, (r2_hidden('#skF_1'('#skF_3', '#skF_4', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_2'), u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_1199])).
% 5.31/1.96  tff(c_50, plain, (![D_184]: (k1_funct_1('#skF_4', D_184)=D_184 | ~r2_hidden(D_184, u1_struct_0('#skF_3')) | ~m1_subset_1(D_184, u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_344])).
% 5.31/1.96  tff(c_1272, plain, (k1_funct_1('#skF_4', '#skF_1'('#skF_3', '#skF_4', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_2'))='#skF_1'('#skF_3', '#skF_4', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_2') | ~m1_subset_1('#skF_1'('#skF_3', '#skF_4', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_2'), u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_1244, c_50])).
% 5.31/1.96  tff(c_1273, plain, (~m1_subset_1('#skF_1'('#skF_3', '#skF_4', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_2'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_1272])).
% 5.31/1.96  tff(c_1314, plain, (~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_1308, c_1273])).
% 5.31/1.96  tff(c_1322, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_58, c_1314])).
% 5.31/1.96  tff(c_1324, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_1322])).
% 5.31/1.96  tff(c_1326, plain, (m1_subset_1('#skF_1'('#skF_3', '#skF_4', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_2'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_1272])).
% 5.31/1.96  tff(c_46, plain, (![A_166, B_170, C_172]: (k1_funct_1(k4_tmap_1(A_166, B_170), C_172)=C_172 | ~r2_hidden(C_172, u1_struct_0(B_170)) | ~m1_subset_1(C_172, u1_struct_0(A_166)) | ~m1_pre_topc(B_170, A_166) | v2_struct_0(B_170) | ~l1_pre_topc(A_166) | ~v2_pre_topc(A_166) | v2_struct_0(A_166))), inference(cnfTransformation, [status(thm)], [f_314])).
% 5.31/1.96  tff(c_1265, plain, (![A_166]: (k1_funct_1(k4_tmap_1(A_166, '#skF_3'), '#skF_1'('#skF_3', '#skF_4', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_2'))='#skF_1'('#skF_3', '#skF_4', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_2') | ~m1_subset_1('#skF_1'('#skF_3', '#skF_4', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_2'), u1_struct_0(A_166)) | ~m1_pre_topc('#skF_3', A_166) | v2_struct_0('#skF_3') | ~l1_pre_topc(A_166) | ~v2_pre_topc(A_166) | v2_struct_0(A_166))), inference(resolution, [status(thm)], [c_1244, c_46])).
% 5.31/1.96  tff(c_1363, plain, (![A_395]: (k1_funct_1(k4_tmap_1(A_395, '#skF_3'), '#skF_1'('#skF_3', '#skF_4', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_2'))='#skF_1'('#skF_3', '#skF_4', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_2') | ~m1_subset_1('#skF_1'('#skF_3', '#skF_4', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_2'), u1_struct_0(A_395)) | ~m1_pre_topc('#skF_3', A_395) | ~l1_pre_topc(A_395) | ~v2_pre_topc(A_395) | v2_struct_0(A_395))), inference(negUnitSimplification, [status(thm)], [c_60, c_1265])).
% 5.31/1.96  tff(c_1369, plain, (k1_funct_1(k4_tmap_1('#skF_2', '#skF_3'), '#skF_1'('#skF_3', '#skF_4', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_2'))='#skF_1'('#skF_3', '#skF_4', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_2') | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_1326, c_1363])).
% 5.31/1.96  tff(c_1373, plain, (k1_funct_1(k4_tmap_1('#skF_2', '#skF_3'), '#skF_1'('#skF_3', '#skF_4', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_2'))='#skF_1'('#skF_3', '#skF_4', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_58, c_1369])).
% 5.31/1.96  tff(c_1374, plain, (k1_funct_1(k4_tmap_1('#skF_2', '#skF_3'), '#skF_1'('#skF_3', '#skF_4', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_2'))='#skF_1'('#skF_3', '#skF_4', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_66, c_1373])).
% 5.31/1.97  tff(c_277, plain, (k3_tmap_1('#skF_3', '#skF_2', '#skF_3', '#skF_3', '#skF_4')='#skF_4' | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_34, c_273])).
% 5.31/1.97  tff(c_283, plain, (k3_tmap_1('#skF_3', '#skF_2', '#skF_3', '#skF_3', '#skF_4')='#skF_4' | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_93, c_277])).
% 5.31/1.97  tff(c_284, plain, (k3_tmap_1('#skF_3', '#skF_2', '#skF_3', '#skF_3', '#skF_4')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_60, c_283])).
% 5.31/1.97  tff(c_1325, plain, (k1_funct_1('#skF_4', '#skF_1'('#skF_3', '#skF_4', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_2'))='#skF_1'('#skF_3', '#skF_4', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_2')), inference(splitRight, [status(thm)], [c_1272])).
% 5.31/1.97  tff(c_363, plain, (![A_81]: (k3_tmap_1(A_81, '#skF_2', '#skF_3', A_81, '#skF_4')=k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', u1_struct_0(A_81)) | ~m1_pre_topc(A_81, '#skF_3') | ~m1_pre_topc('#skF_3', A_81) | ~v2_pre_topc(A_81) | v2_struct_0(A_81) | ~l1_pre_topc(A_81))), inference(resolution, [status(thm)], [c_34, c_358])).
% 5.31/1.97  tff(c_426, plain, (![A_290]: (k3_tmap_1(A_290, '#skF_2', '#skF_3', A_290, '#skF_4')=k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', u1_struct_0(A_290)) | ~m1_pre_topc(A_290, '#skF_3') | ~m1_pre_topc('#skF_3', A_290) | ~v2_pre_topc(A_290) | v2_struct_0(A_290) | ~l1_pre_topc(A_290))), inference(resolution, [status(thm)], [c_34, c_358])).
% 5.31/1.97  tff(c_438, plain, (![A_290]: (m1_subset_1(k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', u1_struct_0(A_290)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_290), u1_struct_0('#skF_2')))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~m1_pre_topc(A_290, A_290) | ~m1_pre_topc('#skF_3', A_290) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_290) | ~v2_pre_topc(A_290) | v2_struct_0(A_290) | ~m1_pre_topc(A_290, '#skF_3') | ~m1_pre_topc('#skF_3', A_290) | ~v2_pre_topc(A_290) | v2_struct_0(A_290) | ~l1_pre_topc(A_290))), inference(superposition, [status(thm), theory('equality')], [c_426, c_20])).
% 5.31/1.97  tff(c_466, plain, (![A_290]: (m1_subset_1(k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', u1_struct_0(A_290)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_290), u1_struct_0('#skF_2')))) | ~m1_pre_topc(A_290, A_290) | v2_struct_0('#skF_2') | ~m1_pre_topc(A_290, '#skF_3') | ~m1_pre_topc('#skF_3', A_290) | ~v2_pre_topc(A_290) | v2_struct_0(A_290) | ~l1_pre_topc(A_290))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_56, c_54, c_52, c_438])).
% 5.31/1.97  tff(c_500, plain, (![A_297]: (m1_subset_1(k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', u1_struct_0(A_297)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_297), u1_struct_0('#skF_2')))) | ~m1_pre_topc(A_297, A_297) | ~m1_pre_topc(A_297, '#skF_3') | ~m1_pre_topc('#skF_3', A_297) | ~v2_pre_topc(A_297) | v2_struct_0(A_297) | ~l1_pre_topc(A_297))), inference(negUnitSimplification, [status(thm)], [c_66, c_466])).
% 5.31/1.97  tff(c_521, plain, (![A_81]: (m1_subset_1(k3_tmap_1(A_81, '#skF_2', '#skF_3', A_81, '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_81), u1_struct_0('#skF_2')))) | ~m1_pre_topc(A_81, A_81) | ~m1_pre_topc(A_81, '#skF_3') | ~m1_pre_topc('#skF_3', A_81) | ~v2_pre_topc(A_81) | v2_struct_0(A_81) | ~l1_pre_topc(A_81) | ~m1_pre_topc(A_81, '#skF_3') | ~m1_pre_topc('#skF_3', A_81) | ~v2_pre_topc(A_81) | v2_struct_0(A_81) | ~l1_pre_topc(A_81))), inference(superposition, [status(thm), theory('equality')], [c_363, c_500])).
% 5.31/1.97  tff(c_1375, plain, (![B_396, D_397, B_398, A_399]: (m1_subset_1('#skF_1'(B_396, D_397, B_398, k4_tmap_1(A_399, B_398), A_399), u1_struct_0(B_396)) | r2_funct_2(u1_struct_0(B_398), u1_struct_0(A_399), k2_tmap_1(B_396, A_399, D_397, B_398), k4_tmap_1(A_399, B_398)) | ~v1_funct_2(k4_tmap_1(A_399, B_398), u1_struct_0(B_398), u1_struct_0(A_399)) | ~v1_funct_1(k4_tmap_1(A_399, B_398)) | ~m1_subset_1(D_397, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_396), u1_struct_0(A_399)))) | ~v1_funct_2(D_397, u1_struct_0(B_396), u1_struct_0(A_399)) | ~v1_funct_1(D_397) | ~m1_pre_topc(B_398, B_396) | v2_struct_0(B_398) | ~l1_pre_topc(B_396) | ~v2_pre_topc(B_396) | v2_struct_0(B_396) | ~m1_pre_topc(B_398, A_399) | ~l1_pre_topc(A_399) | ~v2_pre_topc(A_399) | v2_struct_0(A_399))), inference(resolution, [status(thm)], [c_26, c_676])).
% 5.31/1.97  tff(c_1386, plain, (m1_subset_1('#skF_1'('#skF_3', '#skF_4', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_2'), u1_struct_0('#skF_3')) | r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', k4_tmap_1('#skF_2', '#skF_3')) | ~v1_funct_2(k4_tmap_1('#skF_2', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k4_tmap_1('#skF_2', '#skF_3')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_416, c_1375])).
% 5.31/1.97  tff(c_1391, plain, (m1_subset_1('#skF_1'('#skF_3', '#skF_4', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_2'), u1_struct_0('#skF_3')) | r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', k4_tmap_1('#skF_2', '#skF_3')) | v2_struct_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_58, c_93, c_78, c_377, c_56, c_54, c_52, c_1182, c_1200, c_1386])).
% 5.31/1.97  tff(c_1392, plain, (m1_subset_1('#skF_1'('#skF_3', '#skF_4', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_2'), u1_struct_0('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_66, c_60, c_1245, c_1391])).
% 5.31/1.97  tff(c_4, plain, (![A_4, B_5, C_6, D_7]: (k3_funct_2(A_4, B_5, C_6, D_7)=k1_funct_1(C_6, D_7) | ~m1_subset_1(D_7, A_4) | ~m1_subset_1(C_6, k1_zfmisc_1(k2_zfmisc_1(A_4, B_5))) | ~v1_funct_2(C_6, A_4, B_5) | ~v1_funct_1(C_6) | v1_xboole_0(A_4))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.31/1.97  tff(c_1404, plain, (![B_5, C_6]: (k3_funct_2(u1_struct_0('#skF_3'), B_5, C_6, '#skF_1'('#skF_3', '#skF_4', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_2'))=k1_funct_1(C_6, '#skF_1'('#skF_3', '#skF_4', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_2')) | ~m1_subset_1(C_6, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), B_5))) | ~v1_funct_2(C_6, u1_struct_0('#skF_3'), B_5) | ~v1_funct_1(C_6) | v1_xboole_0(u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_1392, c_4])).
% 5.31/1.97  tff(c_1480, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_1404])).
% 5.31/1.97  tff(c_94, plain, (![B_193, A_194]: (m1_subset_1(u1_struct_0(B_193), k1_zfmisc_1(u1_struct_0(A_194))) | ~m1_pre_topc(B_193, A_194) | ~l1_pre_topc(A_194))), inference(cnfTransformation, [status(thm)], [f_204])).
% 5.31/1.97  tff(c_2, plain, (![C_3, B_2, A_1]: (~v1_xboole_0(C_3) | ~m1_subset_1(B_2, k1_zfmisc_1(C_3)) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.31/1.97  tff(c_97, plain, (![A_194, A_1, B_193]: (~v1_xboole_0(u1_struct_0(A_194)) | ~r2_hidden(A_1, u1_struct_0(B_193)) | ~m1_pre_topc(B_193, A_194) | ~l1_pre_topc(A_194))), inference(resolution, [status(thm)], [c_94, c_2])).
% 5.31/1.97  tff(c_1482, plain, (![A_1, B_193]: (~r2_hidden(A_1, u1_struct_0(B_193)) | ~m1_pre_topc(B_193, '#skF_3') | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_1480, c_97])).
% 5.31/1.97  tff(c_1519, plain, (![A_411, B_412]: (~r2_hidden(A_411, u1_struct_0(B_412)) | ~m1_pre_topc(B_412, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_1482])).
% 5.31/1.97  tff(c_1522, plain, (~m1_pre_topc('#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_1244, c_1519])).
% 5.31/1.97  tff(c_1526, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_377, c_1522])).
% 5.31/1.97  tff(c_1529, plain, (![B_413, C_414]: (k3_funct_2(u1_struct_0('#skF_3'), B_413, C_414, '#skF_1'('#skF_3', '#skF_4', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_2'))=k1_funct_1(C_414, '#skF_1'('#skF_3', '#skF_4', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_2')) | ~m1_subset_1(C_414, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), B_413))) | ~v1_funct_2(C_414, u1_struct_0('#skF_3'), B_413) | ~v1_funct_1(C_414))), inference(splitRight, [status(thm)], [c_1404])).
% 5.31/1.97  tff(c_1533, plain, (k3_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_3', '#skF_2', '#skF_3', '#skF_3', '#skF_4'), '#skF_1'('#skF_3', '#skF_4', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_2'))=k1_funct_1(k3_tmap_1('#skF_3', '#skF_2', '#skF_3', '#skF_3', '#skF_4'), '#skF_1'('#skF_3', '#skF_4', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_2')) | ~v1_funct_2(k3_tmap_1('#skF_3', '#skF_2', '#skF_3', '#skF_3', '#skF_4'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1('#skF_3', '#skF_2', '#skF_3', '#skF_3', '#skF_4')) | ~m1_pre_topc('#skF_3', '#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_521, c_1529])).
% 5.31/1.97  tff(c_1555, plain, (k3_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', '#skF_1'('#skF_3', '#skF_4', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_2'))='#skF_1'('#skF_3', '#skF_4', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_2') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_93, c_377, c_56, c_284, c_54, c_284, c_1325, c_284, c_284, c_1533])).
% 5.31/1.97  tff(c_1556, plain, (k3_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', '#skF_1'('#skF_3', '#skF_4', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_2'))='#skF_1'('#skF_3', '#skF_4', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_60, c_1555])).
% 5.31/1.97  tff(c_36, plain, (![D_138, A_82, B_114, C_130, E_142]: (k3_funct_2(u1_struct_0(B_114), u1_struct_0(A_82), D_138, '#skF_1'(B_114, D_138, C_130, E_142, A_82))!=k1_funct_1(E_142, '#skF_1'(B_114, D_138, C_130, E_142, A_82)) | r2_funct_2(u1_struct_0(C_130), u1_struct_0(A_82), k2_tmap_1(B_114, A_82, D_138, C_130), E_142) | ~m1_subset_1(E_142, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_130), u1_struct_0(A_82)))) | ~v1_funct_2(E_142, u1_struct_0(C_130), u1_struct_0(A_82)) | ~v1_funct_1(E_142) | ~m1_subset_1(D_138, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_114), u1_struct_0(A_82)))) | ~v1_funct_2(D_138, u1_struct_0(B_114), u1_struct_0(A_82)) | ~v1_funct_1(D_138) | ~m1_pre_topc(C_130, B_114) | v2_struct_0(C_130) | ~l1_pre_topc(B_114) | ~v2_pre_topc(B_114) | v2_struct_0(B_114) | ~l1_pre_topc(A_82) | ~v2_pre_topc(A_82) | v2_struct_0(A_82))), inference(cnfTransformation, [status(thm)], [f_252])).
% 5.31/1.97  tff(c_1572, plain, (k1_funct_1(k4_tmap_1('#skF_2', '#skF_3'), '#skF_1'('#skF_3', '#skF_4', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_2'))!='#skF_1'('#skF_3', '#skF_4', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_2') | r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_3'), k4_tmap_1('#skF_2', '#skF_3')) | ~m1_subset_1(k4_tmap_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k4_tmap_1('#skF_2', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k4_tmap_1('#skF_2', '#skF_3')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1556, c_36])).
% 5.31/1.97  tff(c_1576, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', k4_tmap_1('#skF_2', '#skF_3')) | ~m1_subset_1(k4_tmap_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | v2_struct_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_93, c_78, c_377, c_56, c_54, c_52, c_1182, c_1200, c_416, c_1374, c_1572])).
% 5.31/1.97  tff(c_1577, plain, (~m1_subset_1(k4_tmap_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_66, c_60, c_1245, c_1576])).
% 5.31/1.97  tff(c_1581, plain, (~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_26, c_1577])).
% 5.31/1.97  tff(c_1584, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_58, c_1581])).
% 5.31/1.97  tff(c_1586, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_1584])).
% 5.31/1.97  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.31/1.97  
% 5.31/1.97  Inference rules
% 5.31/1.97  ----------------------
% 5.31/1.97  #Ref     : 0
% 5.31/1.97  #Sup     : 308
% 5.31/1.97  #Fact    : 0
% 5.31/1.97  #Define  : 0
% 5.31/1.97  #Split   : 10
% 5.31/1.97  #Chain   : 0
% 5.31/1.97  #Close   : 0
% 5.31/1.97  
% 5.31/1.97  Ordering : KBO
% 5.31/1.97  
% 5.31/1.97  Simplification rules
% 5.31/1.97  ----------------------
% 5.31/1.97  #Subsume      : 34
% 5.31/1.97  #Demod        : 761
% 5.31/1.97  #Tautology    : 100
% 5.31/1.97  #SimpNegUnit  : 123
% 5.31/1.97  #BackRed      : 4
% 5.31/1.97  
% 5.31/1.97  #Partial instantiations: 0
% 5.31/1.97  #Strategies tried      : 1
% 5.31/1.97  
% 5.31/1.97  Timing (in seconds)
% 5.31/1.97  ----------------------
% 5.31/1.97  Preprocessing        : 0.41
% 5.31/1.97  Parsing              : 0.22
% 5.31/1.97  CNF conversion       : 0.04
% 5.31/1.97  Main loop            : 0.77
% 5.31/1.97  Inferencing          : 0.28
% 5.31/1.97  Reduction            : 0.23
% 5.31/1.97  Demodulation         : 0.17
% 5.31/1.97  BG Simplification    : 0.04
% 5.31/1.97  Subsumption          : 0.18
% 5.31/1.97  Abstraction          : 0.04
% 5.31/1.97  MUC search           : 0.00
% 5.31/1.97  Cooper               : 0.00
% 5.31/1.97  Total                : 1.24
% 5.31/1.97  Index Insertion      : 0.00
% 5.31/1.97  Index Deletion       : 0.00
% 5.31/1.97  Index Matching       : 0.00
% 5.31/1.97  BG Taut test         : 0.00
%------------------------------------------------------------------------------
